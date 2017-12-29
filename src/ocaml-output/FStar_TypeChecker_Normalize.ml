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
  fun uu___71_501  ->
    match uu___71_501 with
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
  memoize_lazy: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__strong
let __proj__Mkcfg__item__memoize_lazy: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__memoize_lazy
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
  | Steps of
  (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                     Prims.list)
  FStar_Pervasives_Native.tuple3
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____816 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____852 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____888 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____957 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____999 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1055 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1095 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1127 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1173 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1219 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1244 .
    'Auu____1244 ->
      FStar_Range.range -> 'Auu____1244 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1298 = FStar_ST.op_Bang r in
          match uu____1298 with
          | FStar_Pervasives_Native.Some uu____1375 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1458 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1458 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___72_1465  ->
    match uu___72_1465 with
    | Arg (c,uu____1467,uu____1468) ->
        let uu____1469 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1469
    | MemoLazy uu____1470 -> "MemoLazy"
    | Abs (uu____1477,bs,uu____1479,uu____1480,uu____1481) ->
        let uu____1486 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1486
    | UnivArgs uu____1491 -> "UnivArgs"
    | Match uu____1498 -> "Match"
    | App (uu____1505,t,uu____1507,uu____1508) ->
        let uu____1509 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1509
    | Meta (m,uu____1511) -> "Meta"
    | Let uu____1512 -> "Let"
    | Steps (uu____1521,uu____1522,uu____1523) -> "Steps"
    | Debug (t,uu____1533) ->
        let uu____1534 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1534
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1542 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1542 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1558 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1558 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1571 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1571 then f () else ()
let is_empty: 'Auu____1575 . 'Auu____1575 Prims.list -> Prims.bool =
  fun uu___73_1581  ->
    match uu___73_1581 with | [] -> true | uu____1584 -> false
let lookup_bvar:
  'Auu____1591 'Auu____1592 .
    ('Auu____1592,'Auu____1591) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1591
  =
  fun env  ->
    fun x  ->
      try
        let uu____1616 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1616
      with
      | uu____1629 ->
          let uu____1630 =
            let uu____1631 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1631 in
          failwith uu____1630
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
          let uu____1668 =
            FStar_List.fold_left
              (fun uu____1694  ->
                 fun u1  ->
                   match uu____1694 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1719 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1719 with
                        | (k_u,n1) ->
                            let uu____1734 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1734
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1668 with
          | (uu____1752,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1777 =
                   let uu____1778 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1778 in
                 match uu____1777 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1796 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1805 ->
                   let uu____1806 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1806
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1812 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1821 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1830 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1837 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1837 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1854 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1854 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1862 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1870 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1870 with
                                  | (uu____1875,m) -> n1 <= m)) in
                        if uu____1862 then rest1 else us1
                    | uu____1880 -> us1)
               | uu____1885 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1889 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1889 in
        let uu____1892 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1892
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1894 = aux u in
           match uu____1894 with
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
          (fun uu____1998  ->
             let uu____1999 = FStar_Syntax_Print.tag_of_term t in
             let uu____2000 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1999
               uu____2000);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2007 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2009 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2034 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2035 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2036 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2037 ->
                  let uu____2054 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2054
                  then
                    let uu____2055 =
                      let uu____2056 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2057 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2056 uu____2057 in
                    failwith uu____2055
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2060 =
                    let uu____2061 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2061 in
                  mk uu____2060 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2068 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2068
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2070 = lookup_bvar env x in
                  (match uu____2070 with
                   | Univ uu____2073 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____2076,uu____2077) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2189 = closures_as_binders_delayed cfg env bs in
                  (match uu____2189 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2217 =
                         let uu____2218 =
                           let uu____2235 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2235) in
                         FStar_Syntax_Syntax.Tm_abs uu____2218 in
                       mk uu____2217 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2266 = closures_as_binders_delayed cfg env bs in
                  (match uu____2266 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2308 =
                    let uu____2319 =
                      let uu____2326 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2326] in
                    closures_as_binders_delayed cfg env uu____2319 in
                  (match uu____2308 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2344 =
                         let uu____2345 =
                           let uu____2352 =
                             let uu____2353 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2353
                               FStar_Pervasives_Native.fst in
                           (uu____2352, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2345 in
                       mk uu____2344 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2444 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2444
                    | FStar_Util.Inr c ->
                        let uu____2458 = close_comp cfg env c in
                        FStar_Util.Inr uu____2458 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2474 =
                    let uu____2475 =
                      let uu____2502 = closure_as_term_delayed cfg env t11 in
                      (uu____2502, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2475 in
                  mk uu____2474 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2553 =
                    let uu____2554 =
                      let uu____2561 = closure_as_term_delayed cfg env t' in
                      let uu____2564 =
                        let uu____2565 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2565 in
                      (uu____2561, uu____2564) in
                    FStar_Syntax_Syntax.Tm_meta uu____2554 in
                  mk uu____2553 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2625 =
                    let uu____2626 =
                      let uu____2633 = closure_as_term_delayed cfg env t' in
                      let uu____2636 =
                        let uu____2637 =
                          let uu____2644 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2644) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2637 in
                      (uu____2633, uu____2636) in
                    FStar_Syntax_Syntax.Tm_meta uu____2626 in
                  mk uu____2625 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2663 =
                    let uu____2664 =
                      let uu____2671 = closure_as_term_delayed cfg env t' in
                      let uu____2674 =
                        let uu____2675 =
                          let uu____2684 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2684) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2675 in
                      (uu____2671, uu____2674) in
                    FStar_Syntax_Syntax.Tm_meta uu____2664 in
                  mk uu____2663 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2697 =
                    let uu____2698 =
                      let uu____2705 = closure_as_term_delayed cfg env t' in
                      (uu____2705, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2698 in
                  mk uu____2697 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2745  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2764 =
                    let uu____2775 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2775
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2794 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___92_2806 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___92_2806.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___92_2806.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2794)) in
                  (match uu____2764 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___93_2822 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___93_2822.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___93_2822.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2833,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2892  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2917 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2917
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2937  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2959 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2959
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___94_2971 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___94_2971.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___94_2971.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___95_2972 = lb in
                    let uu____2973 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___95_2972.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___95_2972.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2973
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3003  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3092 =
                    match uu____3092 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3147 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3168 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3228  ->
                                        fun uu____3229  ->
                                          match (uu____3228, uu____3229) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3320 =
                                                norm_pat env3 p1 in
                                              (match uu____3320 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3168 with
                               | (pats1,env3) ->
                                   ((let uu___96_3402 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___96_3402.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___97_3421 = x in
                                let uu____3422 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___97_3421.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___97_3421.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3422
                                } in
                              ((let uu___98_3436 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___98_3436.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___99_3447 = x in
                                let uu____3448 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___99_3447.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___99_3447.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3448
                                } in
                              ((let uu___100_3462 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___100_3462.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___101_3478 = x in
                                let uu____3479 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___101_3478.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___101_3478.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3479
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___102_3486 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___102_3486.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3489 = norm_pat env1 pat in
                        (match uu____3489 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3518 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3518 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3524 =
                    let uu____3525 =
                      let uu____3548 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3548) in
                    FStar_Syntax_Syntax.Tm_match uu____3525 in
                  mk uu____3524 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3634 -> closure_as_term cfg env t
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
        | uu____3660 ->
            FStar_List.map
              (fun uu____3677  ->
                 match uu____3677 with
                 | (x,imp) ->
                     let uu____3696 = closure_as_term_delayed cfg env x in
                     (uu____3696, imp)) args
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
        let uu____3710 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3759  ->
                  fun uu____3760  ->
                    match (uu____3759, uu____3760) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___103_3830 = b in
                          let uu____3831 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___103_3830.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___103_3830.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3831
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3710 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3924 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3937 = closure_as_term_delayed cfg env t in
                 let uu____3938 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3937 uu____3938
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3951 = closure_as_term_delayed cfg env t in
                 let uu____3952 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3951 uu____3952
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
                        (fun uu___74_3978  ->
                           match uu___74_3978 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3982 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3982
                           | f -> f)) in
                 let uu____3986 =
                   let uu___104_3987 = c1 in
                   let uu____3988 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3988;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___104_3987.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3986)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___75_3998  ->
            match uu___75_3998 with
            | FStar_Syntax_Syntax.DECREASES uu____3999 -> false
            | uu____4002 -> true))
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
                   (fun uu___76_4020  ->
                      match uu___76_4020 with
                      | FStar_Syntax_Syntax.DECREASES uu____4021 -> false
                      | uu____4024 -> true)) in
            let rc1 =
              let uu___105_4026 = rc in
              let uu____4027 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___105_4026.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4027;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4034 -> lopt
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
  let arg_as_list u a =
    let uu____4124 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4124 in
  let arg_as_bounded_int uu____4152 =
    match uu____4152 with
    | (a,uu____4164) ->
        let uu____4171 =
          let uu____4172 = FStar_Syntax_Subst.compress a in
          uu____4172.FStar_Syntax_Syntax.n in
        (match uu____4171 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4182;
                FStar_Syntax_Syntax.vars = uu____4183;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4185;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4186;_},uu____4187)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4226 =
               let uu____4231 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4231) in
             FStar_Pervasives_Native.Some uu____4226
         | uu____4236 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4278 = f a in FStar_Pervasives_Native.Some uu____4278
    | uu____4279 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4329 = f a0 a1 in FStar_Pervasives_Native.Some uu____4329
    | uu____4330 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4379 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4379 in
  let binary_op as_a f res args =
    let uu____4435 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4435 in
  let as_primitive_step uu____4459 =
    match uu____4459 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  ->
         fun x  ->
           let uu____4507 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4507) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4535 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4535) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4556 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4556) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4584 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4584) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4612 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4612) in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4729 =
          let uu____4738 = as_a a in
          let uu____4741 = as_b b in (uu____4738, uu____4741) in
        (match uu____4729 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4756 =
               let uu____4757 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4757 in
             FStar_Pervasives_Native.Some uu____4756
         | uu____4758 -> FStar_Pervasives_Native.None)
    | uu____4767 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4781 =
        let uu____4782 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4782 in
      mk uu____4781 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4792 =
      let uu____4795 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4795 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4792 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4827 =
      let uu____4828 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4828 in
    FStar_Syntax_Embeddings.embed_int rng uu____4827 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4846 = arg_as_string a1 in
        (match uu____4846 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4852 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4852 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4865 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4865
              | uu____4866 -> FStar_Pervasives_Native.None)
         | uu____4871 -> FStar_Pervasives_Native.None)
    | uu____4874 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4884 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4884 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4908 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4919 =
          let uu____4940 = arg_as_string fn in
          let uu____4943 = arg_as_int from_line in
          let uu____4946 = arg_as_int from_col in
          let uu____4949 = arg_as_int to_line in
          let uu____4952 = arg_as_int to_col in
          (uu____4940, uu____4943, uu____4946, uu____4949, uu____4952) in
        (match uu____4919 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4983 =
                 let uu____4984 = FStar_BigInt.to_int_fs from_l in
                 let uu____4985 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4984 uu____4985 in
               let uu____4986 =
                 let uu____4987 = FStar_BigInt.to_int_fs to_l in
                 let uu____4988 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4987 uu____4988 in
               FStar_Range.mk_range fn1 uu____4983 uu____4986 in
             let uu____4989 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4989
         | uu____4994 -> FStar_Pervasives_Native.None)
    | uu____5015 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5042)::(a1,uu____5044)::(a2,uu____5046)::[] ->
        let uu____5083 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5083 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5096 -> FStar_Pervasives_Native.None)
    | uu____5097 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5124)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5133 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5157 =
      let uu____5172 =
        let uu____5187 =
          let uu____5202 =
            let uu____5217 =
              let uu____5232 =
                let uu____5247 =
                  let uu____5262 =
                    let uu____5277 =
                      let uu____5292 =
                        let uu____5307 =
                          let uu____5322 =
                            let uu____5337 =
                              let uu____5352 =
                                let uu____5367 =
                                  let uu____5382 =
                                    let uu____5397 =
                                      let uu____5412 =
                                        let uu____5427 =
                                          let uu____5442 =
                                            let uu____5457 =
                                              let uu____5470 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5470,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5477 =
                                              let uu____5492 =
                                                let uu____5505 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5505,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5516 =
                                                let uu____5531 =
                                                  let uu____5546 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5546,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5555 =
                                                  let uu____5572 =
                                                    let uu____5587 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5587,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5596 =
                                                    let uu____5613 =
                                                      let uu____5632 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5632,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5613] in
                                                  uu____5572 :: uu____5596 in
                                                uu____5531 :: uu____5555 in
                                              uu____5492 :: uu____5516 in
                                            uu____5457 :: uu____5477 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5442 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5427 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5412 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5397 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5382 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5850 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5850 y)))
                                  :: uu____5367 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5352 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5337 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5322 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5307 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5292 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5996 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5996)))
                      :: uu____5277 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6022 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____6022)))
                    :: uu____5262 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6048 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____6048)))
                  :: uu____5247 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____6074 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____6074)))
                :: uu____5232 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5217 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5202 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5187 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5172 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5157 in
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
      let uu____6224 =
        let uu____6225 =
          let uu____6226 = FStar_Syntax_Syntax.as_arg c in [uu____6226] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6225 in
      uu____6224 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6261 =
              let uu____6274 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6274, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6294  ->
                        fun uu____6295  ->
                          match (uu____6294, uu____6295) with
                          | ((int_to_t1,x),(uu____6314,y)) ->
                              let uu____6324 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6324))) in
            let uu____6325 =
              let uu____6340 =
                let uu____6353 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6353, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6373  ->
                          fun uu____6374  ->
                            match (uu____6373, uu____6374) with
                            | ((int_to_t1,x),(uu____6393,y)) ->
                                let uu____6403 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6403))) in
              let uu____6404 =
                let uu____6419 =
                  let uu____6432 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6432, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6452  ->
                            fun uu____6453  ->
                              match (uu____6452, uu____6453) with
                              | ((int_to_t1,x),(uu____6472,y)) ->
                                  let uu____6482 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6482))) in
                [uu____6419] in
              uu____6340 :: uu____6404 in
            uu____6261 :: uu____6325)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6572)::(a1,uu____6574)::(a2,uu____6576)::[] ->
        let uu____6613 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6613 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6619 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6619.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6619.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6623 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6623.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6623.FStar_Syntax_Syntax.vars)
                })
         | uu____6624 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6626)::uu____6627::(a1,uu____6629)::(a2,uu____6631)::[] ->
        let uu____6680 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6680 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6686 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6686.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6686.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6690 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6690.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6690.FStar_Syntax_Syntax.vars)
                })
         | uu____6691 -> FStar_Pervasives_Native.None)
    | uu____6692 -> failwith "Unexpected number of arguments" in
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
      let uu____6711 =
        let uu____6712 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6712 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6711
    with | uu____6718 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6722 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6722) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6782  ->
           fun subst1  ->
             match uu____6782 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6823,uu____6824)) ->
                      let uu____6883 = b in
                      (match uu____6883 with
                       | (bv,uu____6891) ->
                           let uu____6892 =
                             let uu____6893 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6893 in
                           if uu____6892
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6898 = unembed_binder term1 in
                              match uu____6898 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6905 =
                                      let uu___110_6906 = bv in
                                      let uu____6907 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___110_6906.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___110_6906.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6907
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6905 in
                                  let b_for_x =
                                    let uu____6911 =
                                      let uu____6918 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6918) in
                                    FStar_Syntax_Syntax.NT uu____6911 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___77_6927  ->
                                         match uu___77_6927 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6928,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6930;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6931;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6936 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6937 -> subst1)) env []
let reduce_primops:
  'Auu____6954 'Auu____6955 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6955) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6954 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6996 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6996
          then tm
          else
            (let uu____6998 = FStar_Syntax_Util.head_and_args tm in
             match uu____6998 with
             | (head1,args) ->
                 let uu____7035 =
                   let uu____7036 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7036.FStar_Syntax_Syntax.n in
                 (match uu____7035 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7040 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7040 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7057  ->
                                   let uu____7058 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7059 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7066 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7058 uu____7059 uu____7066);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7071  ->
                                   let uu____7072 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7072);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7075  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7077 =
                                 prim_step.interpretation psc args in
                               match uu____7077 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7083  ->
                                         let uu____7084 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7084);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7090  ->
                                         let uu____7091 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7092 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7091 uu____7092);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7093 ->
                           (log_primops cfg
                              (fun uu____7097  ->
                                 let uu____7098 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7098);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7102  ->
                            let uu____7103 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7103);
                       (match args with
                        | (a1,uu____7105)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7122 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7134  ->
                            let uu____7135 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7135);
                       (match args with
                        | (a1,uu____7137)::(a2,uu____7139)::[] ->
                            let uu____7166 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____7166 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___111_7170 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___111_7170.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___111_7170.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7173 -> tm))
                  | uu____7182 -> tm))
let reduce_equality:
  'Auu____7187 'Auu____7188 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7188) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7187 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___112_7226 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___112_7226.tcenv);
           delta_level = (uu___112_7226.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___112_7226.strong);
           memoize_lazy = (uu___112_7226.memoize_lazy)
         }) tm
let maybe_simplify_aux:
  'Auu____7233 'Auu____7234 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7234) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7233 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7276 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7276
          then tm1
          else
            (let w t =
               let uu___113_7288 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___113_7288.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___113_7288.FStar_Syntax_Syntax.vars)
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
               | uu____7305 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7310 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7310
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7331 =
                 match uu____7331 with
                 | (t1,q) ->
                     let uu____7344 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7344 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7372 -> (t1, q)) in
               let uu____7381 = FStar_Syntax_Util.head_and_args t in
               match uu____7381 with
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
                         FStar_Syntax_Syntax.pos = uu____7478;
                         FStar_Syntax_Syntax.vars = uu____7479;_},uu____7480);
                    FStar_Syntax_Syntax.pos = uu____7481;
                    FStar_Syntax_Syntax.vars = uu____7482;_},args)
                 ->
                 let uu____7508 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7508
                 then
                   let uu____7509 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7509 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7564)::
                        (uu____7565,(arg,uu____7567))::[] ->
                        maybe_auto_squash arg
                    | (uu____7632,(arg,uu____7634))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7635)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7700)::uu____7701::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7764::(FStar_Pervasives_Native.Some (false
                                   ),uu____7765)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7828 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7844 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7844
                    then
                      let uu____7845 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7845 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7900)::uu____7901::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7964::(FStar_Pervasives_Native.Some (true
                                     ),uu____7965)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8028)::
                          (uu____8029,(arg,uu____8031))::[] ->
                          maybe_auto_squash arg
                      | (uu____8096,(arg,uu____8098))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8099)::[]
                          -> maybe_auto_squash arg
                      | uu____8164 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8180 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8180
                       then
                         let uu____8181 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8181 with
                         | uu____8236::(FStar_Pervasives_Native.Some (true
                                        ),uu____8237)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8300)::uu____8301::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8364)::
                             (uu____8365,(arg,uu____8367))::[] ->
                             maybe_auto_squash arg
                         | (uu____8432,(p,uu____8434))::(uu____8435,(q,uu____8437))::[]
                             ->
                             let uu____8502 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8502
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8504 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8520 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8520
                          then
                            let uu____8521 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8521 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8576)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8615)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8654 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8670 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8670
                             then
                               match args with
                               | (t,uu____8672)::[] ->
                                   let uu____8689 =
                                     let uu____8690 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8690.FStar_Syntax_Syntax.n in
                                   (match uu____8689 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8693::[],body,uu____8695) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8722 -> tm1)
                                    | uu____8725 -> tm1)
                               | (uu____8726,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8727))::
                                   (t,uu____8729)::[] ->
                                   let uu____8768 =
                                     let uu____8769 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8769.FStar_Syntax_Syntax.n in
                                   (match uu____8768 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8772::[],body,uu____8774) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8801 -> tm1)
                                    | uu____8804 -> tm1)
                               | uu____8805 -> tm1
                             else
                               (let uu____8815 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8815
                                then
                                  match args with
                                  | (t,uu____8817)::[] ->
                                      let uu____8834 =
                                        let uu____8835 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8835.FStar_Syntax_Syntax.n in
                                      (match uu____8834 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8838::[],body,uu____8840)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8867 -> tm1)
                                       | uu____8870 -> tm1)
                                  | (uu____8871,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8872))::(t,uu____8874)::[] ->
                                      let uu____8913 =
                                        let uu____8914 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8914.FStar_Syntax_Syntax.n in
                                      (match uu____8913 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8917::[],body,uu____8919)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8946 -> tm1)
                                       | uu____8949 -> tm1)
                                  | uu____8950 -> tm1
                                else
                                  (let uu____8960 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8960
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8961;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8962;_},uu____8963)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8980;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8981;_},uu____8982)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8999 -> tm1
                                   else
                                     (let uu____9009 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____9009 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9029 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9039;
                    FStar_Syntax_Syntax.vars = uu____9040;_},args)
                 ->
                 let uu____9062 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9062
                 then
                   let uu____9063 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9063 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9118)::
                        (uu____9119,(arg,uu____9121))::[] ->
                        maybe_auto_squash arg
                    | (uu____9186,(arg,uu____9188))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9189)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9254)::uu____9255::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9318::(FStar_Pervasives_Native.Some (false
                                   ),uu____9319)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9382 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9398 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9398
                    then
                      let uu____9399 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9399 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9454)::uu____9455::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9518::(FStar_Pervasives_Native.Some (true
                                     ),uu____9519)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9582)::
                          (uu____9583,(arg,uu____9585))::[] ->
                          maybe_auto_squash arg
                      | (uu____9650,(arg,uu____9652))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9653)::[]
                          -> maybe_auto_squash arg
                      | uu____9718 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9734 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9734
                       then
                         let uu____9735 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9735 with
                         | uu____9790::(FStar_Pervasives_Native.Some (true
                                        ),uu____9791)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9854)::uu____9855::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9918)::
                             (uu____9919,(arg,uu____9921))::[] ->
                             maybe_auto_squash arg
                         | (uu____9986,(p,uu____9988))::(uu____9989,(q,uu____9991))::[]
                             ->
                             let uu____10056 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10056
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10058 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10074 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10074
                          then
                            let uu____10075 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10075 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10130)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10169)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10208 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10224 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10224
                             then
                               match args with
                               | (t,uu____10226)::[] ->
                                   let uu____10243 =
                                     let uu____10244 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10244.FStar_Syntax_Syntax.n in
                                   (match uu____10243 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10247::[],body,uu____10249) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10276 -> tm1)
                                    | uu____10279 -> tm1)
                               | (uu____10280,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10281))::
                                   (t,uu____10283)::[] ->
                                   let uu____10322 =
                                     let uu____10323 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10323.FStar_Syntax_Syntax.n in
                                   (match uu____10322 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10326::[],body,uu____10328) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10355 -> tm1)
                                    | uu____10358 -> tm1)
                               | uu____10359 -> tm1
                             else
                               (let uu____10369 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10369
                                then
                                  match args with
                                  | (t,uu____10371)::[] ->
                                      let uu____10388 =
                                        let uu____10389 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10389.FStar_Syntax_Syntax.n in
                                      (match uu____10388 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10392::[],body,uu____10394)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10421 -> tm1)
                                       | uu____10424 -> tm1)
                                  | (uu____10425,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10426))::(t,uu____10428)::[] ->
                                      let uu____10467 =
                                        let uu____10468 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10468.FStar_Syntax_Syntax.n in
                                      (match uu____10467 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10471::[],body,uu____10473)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10500 -> tm1)
                                       | uu____10503 -> tm1)
                                  | uu____10504 -> tm1
                                else
                                  (let uu____10514 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10514
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10515;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10516;_},uu____10517)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10534;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10535;_},uu____10536)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10553 -> tm1
                                   else
                                     (let uu____10563 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10563 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10583 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10592 -> tm1)
let maybe_simplify:
  'Auu____10599 'Auu____10600 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10600) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10599 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10643 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10643
           then
             let uu____10644 = FStar_Syntax_Print.term_to_string tm in
             let uu____10645 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10644 uu____10645
           else ());
          tm'
let is_norm_request:
  'Auu____10651 .
    FStar_Syntax_Syntax.term -> 'Auu____10651 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10664 =
        let uu____10671 =
          let uu____10672 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10672.FStar_Syntax_Syntax.n in
        (uu____10671, args) in
      match uu____10664 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10678::uu____10679::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10683::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10688::uu____10689::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10692 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___78_10703  ->
    match uu___78_10703 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10709 =
          let uu____10712 =
            let uu____10713 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10713 in
          [uu____10712] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10709
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10728 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10728) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10766 =
          let uu____10769 =
            let uu____10774 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10774 s in
          FStar_All.pipe_right uu____10769 FStar_Util.must in
        FStar_All.pipe_right uu____10766 tr_norm_steps in
      match args with
      | uu____10799::(tm,uu____10801)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10824)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10839)::uu____10840::(tm,uu____10842)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10882 =
              let uu____10885 = full_norm steps in parse_steps uu____10885 in
            Beta :: uu____10882 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10894 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___79_10911  ->
    match uu___79_10911 with
    | (App
        (uu____10914,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10915;
                       FStar_Syntax_Syntax.vars = uu____10916;_},uu____10917,uu____10918))::uu____10919
        -> true
    | uu____10926 -> false
let firstn:
  'Auu____10932 .
    Prims.int ->
      'Auu____10932 Prims.list ->
        ('Auu____10932 Prims.list,'Auu____10932 Prims.list)
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
          (uu____10968,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10969;
                         FStar_Syntax_Syntax.vars = uu____10970;_},uu____10971,uu____10972))::uu____10973
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10980 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11096  ->
               let uu____11097 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11098 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11099 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11106 =
                 let uu____11107 =
                   let uu____11110 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11110 in
                 stack_to_string uu____11107 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11097 uu____11098 uu____11099 uu____11106);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11133 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11158 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11175 =
                 let uu____11176 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11177 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11176 uu____11177 in
               failwith uu____11175
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11178 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11195 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11196 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11197;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11198;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11201;
                 FStar_Syntax_Syntax.fv_delta = uu____11202;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11203;
                 FStar_Syntax_Syntax.fv_delta = uu____11204;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11205);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11213 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11213 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11219  ->
                     let uu____11220 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11221 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11220 uu____11221);
                if b
                then
                  (let uu____11222 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11222 t1 fv)
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
                 let uu___114_11261 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___114_11261.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_11261.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11294 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11294) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___115_11302 = cfg in
                 let uu____11303 =
                   FStar_List.filter
                     (fun uu___80_11306  ->
                        match uu___80_11306 with
                        | UnfoldOnly uu____11307 -> false
                        | NoDeltaSteps  -> false
                        | uu____11310 -> true) cfg.steps in
                 {
                   steps = uu____11303;
                   tcenv = (uu___115_11302.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___115_11302.primitive_steps);
                   strong = (uu___115_11302.strong);
                   memoize_lazy = (uu___115_11302.memoize_lazy)
                 } in
               let uu____11311 = get_norm_request (norm cfg' env []) args in
               (match uu____11311 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11327 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___81_11332  ->
                                match uu___81_11332 with
                                | UnfoldUntil uu____11333 -> true
                                | UnfoldOnly uu____11334 -> true
                                | uu____11337 -> false)) in
                      if uu____11327
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___116_11342 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___116_11342.tcenv);
                        delta_level;
                        primitive_steps = (uu___116_11342.primitive_steps);
                        strong = (uu___116_11342.strong);
                        memoize_lazy = (uu___116_11342.memoize_lazy)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____11353 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11353
                      then
                        let uu____11356 =
                          let uu____11357 =
                            let uu____11362 = FStar_Util.now () in
                            (t1, uu____11362) in
                          Debug uu____11357 in
                        uu____11356 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11364;
                  FStar_Syntax_Syntax.vars = uu____11365;_},a1::a2::rest)
               ->
               let uu____11413 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11413 with
                | (hd1,uu____11429) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    norm cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11494;
                  FStar_Syntax_Syntax.vars = uu____11495;_},a1::a2::rest)
               ->
               let uu____11543 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11543 with
                | (hd1,uu____11559) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    norm cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of );
                  FStar_Syntax_Syntax.pos = uu____11624;
                  FStar_Syntax_Syntax.vars = uu____11625;_},a1::a2::a3::rest)
               ->
               let uu____11686 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11686 with
                | (hd1,uu____11702) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1; a2]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a3 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos in
                    norm cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____11773);
                  FStar_Syntax_Syntax.pos = uu____11774;
                  FStar_Syntax_Syntax.vars = uu____11775;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11807 = FStar_List.tl stack in
               norm cfg env uu____11807 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11810;
                  FStar_Syntax_Syntax.vars = uu____11811;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11843 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11843 with
                | (reify_head,uu____11859) ->
                    let a1 =
                      let uu____11881 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11881 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11884);
                            FStar_Syntax_Syntax.pos = uu____11885;
                            FStar_Syntax_Syntax.vars = uu____11886;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11920 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11930 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11930
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11937 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11937
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11940 =
                      let uu____11947 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11947, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11940 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___82_11960  ->
                         match uu___82_11960 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11963 =
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
                 if uu____11963
                 then false
                 else
                   (let uu____11965 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___83_11972  ->
                              match uu___83_11972 with
                              | UnfoldOnly uu____11973 -> true
                              | uu____11976 -> false)) in
                    match uu____11965 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11980 -> should_delta) in
               (log cfg
                  (fun uu____11988  ->
                     let uu____11989 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11990 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11991 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11989 uu____11990 uu____11991);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11994 = lookup_bvar env x in
               (match uu____11994 with
                | Univ uu____11997 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____12046 = FStar_ST.op_Bang r in
                      (match uu____12046 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12193  ->
                                 let uu____12194 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12195 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12194
                                   uu____12195);
                            (let uu____12196 =
                               let uu____12197 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12197.FStar_Syntax_Syntax.n in
                             match uu____12196 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12200 ->
                                 norm cfg env2 stack t'
                             | uu____12217 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12287)::uu____12288 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12297)::uu____12298 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12308,uu____12309))::stack_rest ->
                    (match c with
                     | Univ uu____12313 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12322 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12343  ->
                                    let uu____12344 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12344);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12384  ->
                                    let uu____12385 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12385);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack1 ->
                    norm
                      (let uu___117_12435 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___117_12435.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___117_12435.strong);
                         memoize_lazy = (uu___117_12435.memoize_lazy)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____12476  ->
                          let uu____12477 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12477);
                     norm cfg env stack1 t1)
                | (Debug uu____12478)::uu____12479 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12486 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12486
                    else
                      (let uu____12488 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12488 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12530  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12558 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12558
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12568 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12568)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12573 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12573.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12573.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12574 -> lopt in
                           (log cfg
                              (fun uu____12580  ->
                                 let uu____12581 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12581);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12594 = cfg in
                               {
                                 steps = (uu___119_12594.steps);
                                 tcenv = (uu___119_12594.tcenv);
                                 delta_level = (uu___119_12594.delta_level);
                                 primitive_steps =
                                   (uu___119_12594.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12594.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12605)::uu____12606 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12613 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12613
                    else
                      (let uu____12615 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12615 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12657  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12685 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12685
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12695 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12695)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12700 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12700.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12700.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12701 -> lopt in
                           (log cfg
                              (fun uu____12707  ->
                                 let uu____12708 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12708);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12721 = cfg in
                               {
                                 steps = (uu___119_12721.steps);
                                 tcenv = (uu___119_12721.tcenv);
                                 delta_level = (uu___119_12721.delta_level);
                                 primitive_steps =
                                   (uu___119_12721.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12721.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12732)::uu____12733 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12744 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12744
                    else
                      (let uu____12746 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12746 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12788  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12816 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12816
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12826 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12826)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12831 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12831.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12831.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12832 -> lopt in
                           (log cfg
                              (fun uu____12838  ->
                                 let uu____12839 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12839);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12852 = cfg in
                               {
                                 steps = (uu___119_12852.steps);
                                 tcenv = (uu___119_12852.tcenv);
                                 delta_level = (uu___119_12852.delta_level);
                                 primitive_steps =
                                   (uu___119_12852.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12852.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12863)::uu____12864 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12875 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12875
                    else
                      (let uu____12877 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12877 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12919  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12947 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12947
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12957 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12957)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12962 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12962.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12962.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12963 -> lopt in
                           (log cfg
                              (fun uu____12969  ->
                                 let uu____12970 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12970);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12983 = cfg in
                               {
                                 steps = (uu___119_12983.steps);
                                 tcenv = (uu___119_12983.tcenv);
                                 delta_level = (uu___119_12983.delta_level);
                                 primitive_steps =
                                   (uu___119_12983.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12983.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12994)::uu____12995 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13010 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13010
                    else
                      (let uu____13012 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13012 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13054  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13082 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13082
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13092 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13092)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_13097 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_13097.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_13097.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13098 -> lopt in
                           (log cfg
                              (fun uu____13104  ->
                                 let uu____13105 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13105);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_13118 = cfg in
                               {
                                 steps = (uu___119_13118.steps);
                                 tcenv = (uu___119_13118.tcenv);
                                 delta_level = (uu___119_13118.delta_level);
                                 primitive_steps =
                                   (uu___119_13118.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_13118.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13129 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13129
                    else
                      (let uu____13131 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13131 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13173  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13201 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13201
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13211 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13211)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_13216 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_13216.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_13216.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13217 -> lopt in
                           (log cfg
                              (fun uu____13223  ->
                                 let uu____13224 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13224);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_13237 = cfg in
                               {
                                 steps = (uu___119_13237.steps);
                                 tcenv = (uu___119_13237.tcenv);
                                 delta_level = (uu___119_13237.delta_level);
                                 primitive_steps =
                                   (uu___119_13237.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_13237.memoize_lazy)
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
                      (fun uu____13286  ->
                         fun stack1  ->
                           match uu____13286 with
                           | (a,aq) ->
                               let uu____13298 =
                                 let uu____13299 =
                                   let uu____13306 =
                                     let uu____13307 =
                                       let uu____13338 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13338, false) in
                                     Clos uu____13307 in
                                   (uu____13306, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13299 in
                               uu____13298 :: stack1) args) in
               (log cfg
                  (fun uu____13422  ->
                     let uu____13423 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13423);
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
                             ((let uu___120_13459 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_13459.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_13459.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13460 ->
                      let uu____13465 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13465)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13468 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13468 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13499 =
                          let uu____13500 =
                            let uu____13507 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_13509 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_13509.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_13509.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13507) in
                          FStar_Syntax_Syntax.Tm_refine uu____13500 in
                        mk uu____13499 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13528 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13528
               else
                 (let uu____13530 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13530 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13538 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13562  -> dummy :: env1) env) in
                        norm_comp cfg uu____13538 c1 in
                      let t2 =
                        let uu____13584 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13584 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13643)::uu____13644 ->
                    (log cfg
                       (fun uu____13655  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13656)::uu____13657 ->
                    (log cfg
                       (fun uu____13668  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13669,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13670;
                                   FStar_Syntax_Syntax.vars = uu____13671;_},uu____13672,uu____13673))::uu____13674
                    ->
                    (log cfg
                       (fun uu____13683  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13684)::uu____13685 ->
                    (log cfg
                       (fun uu____13696  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13697 ->
                    (log cfg
                       (fun uu____13700  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13704  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13721 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13721
                         | FStar_Util.Inr c ->
                             let uu____13729 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13729 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Steps (s,ps,dl))::stack1 ->
                           let t2 =
                             let uu____13752 =
                               let uu____13753 =
                                 let uu____13780 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13780, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13753 in
                             mk uu____13752 t1.FStar_Syntax_Syntax.pos in
                           norm
                             (let uu___122_13801 = cfg in
                              {
                                steps = s;
                                tcenv = (uu___122_13801.tcenv);
                                delta_level = dl;
                                primitive_steps = ps;
                                strong = (uu___122_13801.strong);
                                memoize_lazy = (uu___122_13801.memoize_lazy)
                              }) env stack1 t2
                       | uu____13802 ->
                           let uu____13803 =
                             let uu____13804 =
                               let uu____13805 =
                                 let uu____13832 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13832, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13805 in
                             mk uu____13804 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13803))))
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
                         let uu____13942 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13942 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___123_13962 = cfg in
                               let uu____13963 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___123_13962.steps);
                                 tcenv = uu____13963;
                                 delta_level = (uu___123_13962.delta_level);
                                 primitive_steps =
                                   (uu___123_13962.primitive_steps);
                                 strong = (uu___123_13962.strong);
                                 memoize_lazy = (uu___123_13962.memoize_lazy)
                               } in
                             let norm1 t2 =
                               let uu____13968 =
                                 let uu____13969 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13969 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13968 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___124_13972 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___124_13972.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___124_13972.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13973 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13973
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13984,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13985;
                               FStar_Syntax_Syntax.lbunivs = uu____13986;
                               FStar_Syntax_Syntax.lbtyp = uu____13987;
                               FStar_Syntax_Syntax.lbeff = uu____13988;
                               FStar_Syntax_Syntax.lbdef = uu____13989;_}::uu____13990),uu____13991)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____14027 =
                 (let uu____14030 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____14030) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____14032 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____14032))) in
               if uu____14027
               then
                 let binder =
                   let uu____14034 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____14034 in
                 let env1 =
                   let uu____14044 =
                     let uu____14051 =
                       let uu____14052 =
                         let uu____14083 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14083,
                           false) in
                       Clos uu____14052 in
                     ((FStar_Pervasives_Native.Some binder), uu____14051) in
                   uu____14044 :: env in
                 (log cfg
                    (fun uu____14176  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____14178 =
                    let uu____14183 =
                      let uu____14184 =
                        let uu____14185 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14185
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14184] in
                    FStar_Syntax_Subst.open_term uu____14183 body in
                  match uu____14178 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____14194  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____14202 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____14202 in
                          FStar_Util.Inl
                            (let uu___125_14212 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___125_14212.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___125_14212.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____14215  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___126_14217 = lb in
                           let uu____14218 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___126_14217.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___126_14217.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____14218
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____14253  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___127_14273 = cfg in
                           {
                             steps = (uu___127_14273.steps);
                             tcenv = (uu___127_14273.tcenv);
                             delta_level = (uu___127_14273.delta_level);
                             primitive_steps =
                               (uu___127_14273.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___127_14273.memoize_lazy)
                           } in
                         log cfg1
                           (fun uu____14276  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- body\n");
                         norm cfg1 env'
                           ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                           :: stack) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____14293 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14293 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14329 =
                               let uu___128_14330 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___128_14330.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___128_14330.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14329 in
                           let uu____14331 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14331 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14357 =
                                   FStar_List.map (fun uu____14373  -> dummy)
                                     lbs1 in
                                 let uu____14374 =
                                   let uu____14383 =
                                     FStar_List.map
                                       (fun uu____14403  -> dummy) xs1 in
                                   FStar_List.append uu____14383 env in
                                 FStar_List.append uu____14357 uu____14374 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14427 =
                                       let uu___129_14428 = rc in
                                       let uu____14429 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___129_14428.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14429;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___129_14428.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14427
                                 | uu____14436 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___130_14440 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___130_14440.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___130_14440.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14450 =
                        FStar_List.map (fun uu____14466  -> dummy) lbs2 in
                      FStar_List.append uu____14450 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14474 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14474 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___131_14490 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___131_14490.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___131_14490.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14517 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14517
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14536 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14612  ->
                        match uu____14612 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___132_14733 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___132_14733.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___132_14733.FStar_Syntax_Syntax.sort)
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
               (match uu____14536 with
                | (rec_env,memos,uu____14946) ->
                    let uu____14999 =
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
                             let uu____15542 =
                               let uu____15549 =
                                 let uu____15550 =
                                   let uu____15581 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15581, false) in
                                 Clos uu____15550 in
                               (FStar_Pervasives_Native.None, uu____15549) in
                             uu____15542 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15694 =
                      let uu____15695 = should_reify cfg stack in
                      Prims.op_Negation uu____15695 in
                    if uu____15694
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____15705 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15705
                        then
                          let uu___133_15706 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___133_15706.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___133_15706.primitive_steps);
                            strong = (uu___133_15706.strong);
                            memoize_lazy = (uu___133_15706.memoize_lazy)
                          }
                        else
                          (let uu___134_15708 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___134_15708.tcenv);
                             delta_level = (uu___134_15708.delta_level);
                             primitive_steps =
                               (uu___134_15708.primitive_steps);
                             strong = (uu___134_15708.strong);
                             memoize_lazy = (uu___134_15708.memoize_lazy)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15710 =
                         let uu____15711 = FStar_Syntax_Subst.compress head1 in
                         uu____15711.FStar_Syntax_Syntax.n in
                       match uu____15710 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15729 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15729 with
                            | (uu____15730,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15736 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15744 =
                                         let uu____15745 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15745.FStar_Syntax_Syntax.n in
                                       match uu____15744 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15751,uu____15752))
                                           ->
                                           let uu____15761 =
                                             let uu____15762 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15762.FStar_Syntax_Syntax.n in
                                           (match uu____15761 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15768,msrc,uu____15770))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15779 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15779
                                            | uu____15780 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15781 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15782 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15782 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___135_15787 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___135_15787.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___135_15787.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___135_15787.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15788 =
                                            FStar_List.tl stack in
                                          let uu____15789 =
                                            let uu____15790 =
                                              let uu____15793 =
                                                let uu____15794 =
                                                  let uu____15807 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15807) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15794 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15793 in
                                            uu____15790
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15788
                                            uu____15789
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15823 =
                                            let uu____15824 = is_return body in
                                            match uu____15824 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15828;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15829;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15834 -> false in
                                          if uu____15823
                                          then
                                            norm cfg env stack
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let head2 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef in
                                             let body1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body in
                                             let body_rc =
                                               {
                                                 FStar_Syntax_Syntax.residual_effect
                                                   = m1;
                                                 FStar_Syntax_Syntax.residual_typ
                                                   =
                                                   (FStar_Pervasives_Native.Some
                                                      t2);
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               } in
                                             let body2 =
                                               let uu____15858 =
                                                 let uu____15861 =
                                                   let uu____15862 =
                                                     let uu____15879 =
                                                       let uu____15882 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15882] in
                                                     (uu____15879, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15862 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15861 in
                                               uu____15858
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15898 =
                                                 let uu____15899 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15899.FStar_Syntax_Syntax.n in
                                               match uu____15898 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15905::uu____15906::[])
                                                   ->
                                                   let uu____15913 =
                                                     let uu____15916 =
                                                       let uu____15917 =
                                                         let uu____15924 =
                                                           let uu____15927 =
                                                             let uu____15928
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15928 in
                                                           let uu____15929 =
                                                             let uu____15932
                                                               =
                                                               let uu____15933
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15933 in
                                                             [uu____15932] in
                                                           uu____15927 ::
                                                             uu____15929 in
                                                         (bind1, uu____15924) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15917 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15916 in
                                                   uu____15913
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15941 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15947 =
                                                 let uu____15950 =
                                                   let uu____15951 =
                                                     let uu____15966 =
                                                       let uu____15969 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15970 =
                                                         let uu____15973 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15974 =
                                                           let uu____15977 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15978 =
                                                             let uu____15981
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15982
                                                               =
                                                               let uu____15985
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15986
                                                                 =
                                                                 let uu____15989
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15989] in
                                                               uu____15985 ::
                                                                 uu____15986 in
                                                             uu____15981 ::
                                                               uu____15982 in
                                                           uu____15977 ::
                                                             uu____15978 in
                                                         uu____15973 ::
                                                           uu____15974 in
                                                       uu____15969 ::
                                                         uu____15970 in
                                                     (bind_inst, uu____15966) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15951 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15950 in
                                               uu____15947
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15997 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____15997 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____16021 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____16021 with
                            | (uu____16022,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____16057 =
                                        let uu____16058 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____16058.FStar_Syntax_Syntax.n in
                                      match uu____16057 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____16064) -> t4
                                      | uu____16069 -> head2 in
                                    let uu____16070 =
                                      let uu____16071 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____16071.FStar_Syntax_Syntax.n in
                                    match uu____16070 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____16077 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____16078 = maybe_extract_fv head2 in
                                  match uu____16078 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____16088 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____16088
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____16093 =
                                          maybe_extract_fv head3 in
                                        match uu____16093 with
                                        | FStar_Pervasives_Native.Some
                                            uu____16098 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____16099 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____16104 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____16119 =
                                    match uu____16119 with
                                    | (e,q) ->
                                        let uu____16126 =
                                          let uu____16127 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____16127.FStar_Syntax_Syntax.n in
                                        (match uu____16126 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____16142 -> false) in
                                  let uu____16143 =
                                    let uu____16144 =
                                      let uu____16151 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____16151 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____16144 in
                                  if uu____16143
                                  then
                                    let uu____16156 =
                                      let uu____16157 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____16157 in
                                    failwith uu____16156
                                  else ());
                                 (let uu____16159 =
                                    maybe_unfold_action head_app in
                                  match uu____16159 with
                                  | (head_app1,found_action) ->
                                      let mk1 tm =
                                        FStar_Syntax_Syntax.mk tm
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos in
                                      let body =
                                        mk1
                                          (FStar_Syntax_Syntax.Tm_app
                                             (head_app1, args)) in
                                      let body1 =
                                        match found_action with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Syntax_Util.mk_reify body
                                        | FStar_Pervasives_Native.Some (false
                                            ) ->
                                            mk1
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (body,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      (m1, t2))))
                                        | FStar_Pervasives_Native.Some (true
                                            ) -> body in
                                      let uu____16198 = FStar_List.tl stack in
                                      norm cfg env uu____16198 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16212 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16212 in
                           let uu____16213 = FStar_List.tl stack in
                           norm cfg env uu____16213 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16334  ->
                                     match uu____16334 with
                                     | (pat,wopt,tm) ->
                                         let uu____16382 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16382))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16414 = FStar_List.tl stack in
                           norm cfg env uu____16414 tm
                       | uu____16415 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16423 = should_reify cfg stack in
                    if uu____16423
                    then
                      let uu____16424 = FStar_List.tl stack in
                      let uu____16425 =
                        let uu____16426 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16426 in
                      norm cfg env uu____16424 uu____16425
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16429 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16429
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___136_16438 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___136_16438.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___136_16438.primitive_steps);
                             strong = (uu___136_16438.strong);
                             memoize_lazy = (uu___136_16438.memoize_lazy)
                           } in
                         norm cfg1 env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack1)
                           head1
                       else
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack)
                           head1)
                | uu____16440 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____16442::uu____16443 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16448) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16449 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____16480 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16494 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16494
                             | uu____16505 -> m in
                           let t2 =
                             mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack t2)))
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
              let uu____16517 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16517 in
            let uu____16518 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16518 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16531  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16542  ->
                      let uu____16543 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16544 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16543
                        uu____16544);
                 (let t1 =
                    let uu____16546 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16546
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
                    | (UnivArgs (us',uu____16556))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____16611 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____16614 ->
                        let uu____16617 =
                          let uu____16618 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16618 in
                        failwith uu____16617
                  else norm cfg env stack t1))
and reify_lift:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
              let uu____16628 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16628 with
              | (uu____16629,return_repr) ->
                  let return_inst =
                    let uu____16638 =
                      let uu____16639 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16639.FStar_Syntax_Syntax.n in
                    match uu____16638 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16645::[]) ->
                        let uu____16652 =
                          let uu____16655 =
                            let uu____16656 =
                              let uu____16663 =
                                let uu____16666 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16666] in
                              (return_tm, uu____16663) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16656 in
                          FStar_Syntax_Syntax.mk uu____16655 in
                        uu____16652 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16674 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16677 =
                    let uu____16680 =
                      let uu____16681 =
                        let uu____16696 =
                          let uu____16699 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16700 =
                            let uu____16703 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16703] in
                          uu____16699 :: uu____16700 in
                        (return_inst, uu____16696) in
                      FStar_Syntax_Syntax.Tm_app uu____16681 in
                    FStar_Syntax_Syntax.mk uu____16680 in
                  uu____16677 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16712 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16712 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16715 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16715
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16716;
                     FStar_TypeChecker_Env.mtarget = uu____16717;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16718;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16733;
                     FStar_TypeChecker_Env.mtarget = uu____16734;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16735;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16759 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16760 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16759 t FStar_Syntax_Syntax.tun uu____16760)
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
                (fun uu____16816  ->
                   match uu____16816 with
                   | (a,imp) ->
                       let uu____16827 = norm cfg env [] a in
                       (uu____16827, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___137_16844 = comp1 in
            let uu____16847 =
              let uu____16848 =
                let uu____16857 = norm cfg env [] t in
                let uu____16858 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16857, uu____16858) in
              FStar_Syntax_Syntax.Total uu____16848 in
            {
              FStar_Syntax_Syntax.n = uu____16847;
              FStar_Syntax_Syntax.pos =
                (uu___137_16844.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16844.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___138_16873 = comp1 in
            let uu____16876 =
              let uu____16877 =
                let uu____16886 = norm cfg env [] t in
                let uu____16887 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16886, uu____16887) in
              FStar_Syntax_Syntax.GTotal uu____16877 in
            {
              FStar_Syntax_Syntax.n = uu____16876;
              FStar_Syntax_Syntax.pos =
                (uu___138_16873.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___138_16873.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16939  ->
                      match uu____16939 with
                      | (a,i) ->
                          let uu____16950 = norm cfg env [] a in
                          (uu____16950, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___84_16961  ->
                      match uu___84_16961 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16965 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16965
                      | f -> f)) in
            let uu___139_16969 = comp1 in
            let uu____16972 =
              let uu____16973 =
                let uu___140_16974 = ct in
                let uu____16975 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16976 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16979 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16975;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___140_16974.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16976;
                  FStar_Syntax_Syntax.effect_args = uu____16979;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16973 in
            {
              FStar_Syntax_Syntax.n = uu____16972;
              FStar_Syntax_Syntax.pos =
                (uu___139_16969.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_16969.FStar_Syntax_Syntax.vars)
            }
and ghost_to_pure_aux:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        let norm1 t =
          norm
            (let uu___141_16997 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses;
                 EraseUniverses];
               tcenv = (uu___141_16997.tcenv);
               delta_level =
                 [FStar_TypeChecker_Env.Unfold
                    FStar_Syntax_Syntax.Delta_constant];
               primitive_steps = (uu___141_16997.primitive_steps);
               strong = (uu___141_16997.strong);
               memoize_lazy = false
             }) env [] t in
        let non_info t =
          let uu____17002 = norm1 t in
          FStar_Syntax_Util.non_informative uu____17002 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____17005 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___142_17024 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___142_17024.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___142_17024.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____17031 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____17031
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
                    let uu___143_17042 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___143_17042.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___143_17042.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___143_17042.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags1
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___144_17044 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___144_17044.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___144_17044.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___144_17044.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___144_17044.FStar_Syntax_Syntax.flags)
                    } in
              let uu___145_17045 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___145_17045.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___145_17045.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____17047 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____17050  ->
        match uu____17050 with
        | (x,imp) ->
            let uu____17053 =
              let uu___146_17054 = x in
              let uu____17055 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___146_17054.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___146_17054.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17055
              } in
            (uu____17053, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17061 =
          FStar_List.fold_left
            (fun uu____17079  ->
               fun b  ->
                 match uu____17079 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____17061 with | (nbs,uu____17119) -> FStar_List.rev nbs
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
            let uu____17135 =
              let uu___147_17136 = rc in
              let uu____17137 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___147_17136.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17137;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___147_17136.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17135
        | uu____17144 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17157  ->
               let uu____17158 = FStar_Syntax_Print.tag_of_term t in
               let uu____17159 = FStar_Syntax_Print.term_to_string t in
               let uu____17160 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17167 =
                 let uu____17168 =
                   let uu____17171 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17171 in
                 stack_to_string uu____17168 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____17158 uu____17159 uu____17160 uu____17167);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____17200 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____17200
                 then
                   let time_now = FStar_Util.now () in
                   let uu____17202 =
                     let uu____17203 =
                       let uu____17204 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17204 in
                     FStar_Util.string_of_int uu____17203 in
                   let uu____17209 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17210 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17202 uu____17209 uu____17210
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___148_17228 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___148_17228.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___148_17228.strong);
                    memoize_lazy = (uu___148_17228.memoize_lazy)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____17277  ->
                     let uu____17278 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17278);
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
               let uu____17314 =
                 let uu___149_17315 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___149_17315.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___149_17315.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____17314
           | (Arg (Univ uu____17316,uu____17317,uu____17318))::uu____17319 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17322,uu____17323))::uu____17324 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____17340),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17393  ->
                     let uu____17394 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17394);
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
                  (let uu____17404 = FStar_ST.op_Bang m in
                   match uu____17404 with
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
                   | FStar_Pervasives_Native.Some (uu____17570,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17613 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17613
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17625  ->
                     let uu____17626 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17626);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17631 =
                   log cfg
                     (fun uu____17636  ->
                        let uu____17637 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17638 =
                          let uu____17639 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17656  ->
                                    match uu____17656 with
                                    | (p,uu____17666,uu____17667) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17639
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17637 uu____17638);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___85_17684  ->
                                match uu___85_17684 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17685 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___150_17689 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___150_17689.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___150_17689.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___150_17689.memoize_lazy)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17721 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17742 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17802  ->
                                    fun uu____17803  ->
                                      match (uu____17802, uu____17803) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17894 = norm_pat env3 p1 in
                                          (match uu____17894 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17742 with
                           | (pats1,env3) ->
                               ((let uu___151_17976 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___151_17976.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___152_17995 = x in
                            let uu____17996 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_17995.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_17995.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17996
                            } in
                          ((let uu___153_18010 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___153_18010.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___154_18021 = x in
                            let uu____18022 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___154_18021.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___154_18021.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18022
                            } in
                          ((let uu___155_18036 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___155_18036.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___156_18052 = x in
                            let uu____18053 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___156_18052.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___156_18052.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18053
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___157_18060 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___157_18060.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18070 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18084 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____18084 with
                                  | (p,wopt,e) ->
                                      let uu____18104 = norm_pat env1 p in
                                      (match uu____18104 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18129 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18129 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____18135 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____18135) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18145) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18150 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18151;
                         FStar_Syntax_Syntax.fv_delta = uu____18152;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18153;
                         FStar_Syntax_Syntax.fv_delta = uu____18154;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18155);_}
                       -> true
                   | uu____18162 -> false in
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
                   let uu____18307 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18307 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18394 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18433 ->
                                 let uu____18434 =
                                   let uu____18435 = is_cons head1 in
                                   Prims.op_Negation uu____18435 in
                                 FStar_Util.Inr uu____18434)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18460 =
                              let uu____18461 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18461.FStar_Syntax_Syntax.n in
                            (match uu____18460 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18479 ->
                                 let uu____18480 =
                                   let uu____18481 = is_cons head1 in
                                   Prims.op_Negation uu____18481 in
                                 FStar_Util.Inr uu____18480))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18550)::rest_a,(p1,uu____18553)::rest_p) ->
                       let uu____18597 = matches_pat t1 p1 in
                       (match uu____18597 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18646 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18752 = matches_pat scrutinee1 p1 in
                       (match uu____18752 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18792  ->
                                  let uu____18793 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18794 =
                                    let uu____18795 =
                                      FStar_List.map
                                        (fun uu____18805  ->
                                           match uu____18805 with
                                           | (uu____18810,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18795
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18793 uu____18794);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18841  ->
                                       match uu____18841 with
                                       | (bv,t1) ->
                                           let uu____18864 =
                                             let uu____18871 =
                                               let uu____18874 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18874 in
                                             let uu____18875 =
                                               let uu____18876 =
                                                 let uu____18907 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18907, false) in
                                               Clos uu____18876 in
                                             (uu____18871, uu____18875) in
                                           uu____18864 :: env2) env1 s in
                              let uu____19024 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____19024))) in
                 let uu____19025 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____19025
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___86_19046  ->
                match uu___86_19046 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____19050 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____19056 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true
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
            let uu___158_19081 = config s e in
            {
              steps = (uu___158_19081.steps);
              tcenv = (uu___158_19081.tcenv);
              delta_level = (uu___158_19081.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___158_19081.strong);
              memoize_lazy = (uu___158_19081.memoize_lazy)
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
      fun t  -> let uu____19106 = config s e in norm_comp uu____19106 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____19119 = config [] env in norm_universe uu____19119 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____19132 = config [] env in ghost_to_pure_aux uu____19132 [] c
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
        let uu____19150 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____19150 in
      let uu____19157 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____19157
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___159_19159 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___159_19159.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___159_19159.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____19162  ->
                    let uu____19163 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____19163))
            }
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
            ((let uu____19180 =
                let uu____19185 =
                  let uu____19186 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19186 in
                (FStar_Errors.Warning_NormalizationFailure, uu____19185) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____19180);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19197 = config [AllowUnboundUniverses] env in
          norm_comp uu____19197 [] c
        with
        | e ->
            ((let uu____19210 =
                let uu____19215 =
                  let uu____19216 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19216 in
                (FStar_Errors.Warning_NormalizationFailure, uu____19215) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____19210);
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
                   let uu____19253 =
                     let uu____19254 =
                       let uu____19261 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____19261) in
                     FStar_Syntax_Syntax.Tm_refine uu____19254 in
                   mk uu____19253 t01.FStar_Syntax_Syntax.pos
               | uu____19266 -> t2)
          | uu____19267 -> t2 in
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
        let uu____19307 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19307 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19336 ->
                 let uu____19343 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19343 with
                  | (actuals,uu____19353,uu____19354) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19368 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19368 with
                         | (binders,args) ->
                             let uu____19385 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19385
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
      | uu____19393 ->
          let uu____19394 = FStar_Syntax_Util.head_and_args t in
          (match uu____19394 with
           | (head1,args) ->
               let uu____19431 =
                 let uu____19432 = FStar_Syntax_Subst.compress head1 in
                 uu____19432.FStar_Syntax_Syntax.n in
               (match uu____19431 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19435,thead) ->
                    let uu____19461 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19461 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19503 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___164_19511 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___164_19511.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___164_19511.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___164_19511.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___164_19511.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___164_19511.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___164_19511.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___164_19511.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___164_19511.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___164_19511.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___164_19511.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___164_19511.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___164_19511.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___164_19511.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___164_19511.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___164_19511.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___164_19511.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___164_19511.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___164_19511.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___164_19511.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___164_19511.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___164_19511.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___164_19511.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___164_19511.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___164_19511.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___164_19511.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___164_19511.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___164_19511.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___164_19511.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___164_19511.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___164_19511.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___164_19511.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19503 with
                            | (uu____19512,ty,uu____19514) ->
                                eta_expand_with_type env t ty))
                | uu____19515 ->
                    let uu____19516 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___165_19524 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___165_19524.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___165_19524.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___165_19524.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___165_19524.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___165_19524.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___165_19524.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___165_19524.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___165_19524.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___165_19524.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___165_19524.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___165_19524.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___165_19524.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___165_19524.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___165_19524.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___165_19524.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___165_19524.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___165_19524.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___165_19524.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___165_19524.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___165_19524.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___165_19524.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___165_19524.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___165_19524.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___165_19524.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___165_19524.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___165_19524.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___165_19524.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___165_19524.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___165_19524.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___165_19524.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___165_19524.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19516 with
                     | (uu____19525,ty,uu____19527) ->
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
            | (uu____19601,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19607,FStar_Util.Inl t) ->
                let uu____19613 =
                  let uu____19616 =
                    let uu____19617 =
                      let uu____19630 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19630) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19617 in
                  FStar_Syntax_Syntax.mk uu____19616 in
                uu____19613 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19634 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19634 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19661 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19716 ->
                    let uu____19717 =
                      let uu____19726 =
                        let uu____19727 = FStar_Syntax_Subst.compress t3 in
                        uu____19727.FStar_Syntax_Syntax.n in
                      (uu____19726, tc) in
                    (match uu____19717 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19752) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19789) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19828,FStar_Util.Inl uu____19829) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19852 -> failwith "Impossible") in
              (match uu____19661 with
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
          let uu____19957 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19957 with
          | (univ_names1,binders1,tc) ->
              let uu____20015 = FStar_Util.left tc in
              (univ_names1, binders1, uu____20015)
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
          let uu____20050 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20050 with
          | (univ_names1,binders1,tc) ->
              let uu____20110 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20110)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20143 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20143 with
           | (univ_names1,binders1,typ1) ->
               let uu___166_20171 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___166_20171.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___166_20171.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___166_20171.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___166_20171.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___167_20192 = s in
          let uu____20193 =
            let uu____20194 =
              let uu____20203 = FStar_List.map (elim_uvars env) sigs in
              (uu____20203, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20194 in
          {
            FStar_Syntax_Syntax.sigel = uu____20193;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_20192.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_20192.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_20192.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_20192.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20220 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20220 with
           | (univ_names1,uu____20238,typ1) ->
               let uu___168_20252 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_20252.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_20252.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_20252.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_20252.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20258 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20258 with
           | (univ_names1,uu____20276,typ1) ->
               let uu___169_20290 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___169_20290.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___169_20290.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___169_20290.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___169_20290.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20324 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20324 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20347 =
                            let uu____20348 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20348 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20347 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___170_20351 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___170_20351.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___170_20351.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___171_20352 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___171_20352.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___171_20352.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___171_20352.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___171_20352.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___172_20364 = s in
          let uu____20365 =
            let uu____20366 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20366 in
          {
            FStar_Syntax_Syntax.sigel = uu____20365;
            FStar_Syntax_Syntax.sigrng =
              (uu___172_20364.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___172_20364.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___172_20364.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___172_20364.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20370 = elim_uvars_aux_t env us [] t in
          (match uu____20370 with
           | (us1,uu____20388,t1) ->
               let uu___173_20402 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___173_20402.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___173_20402.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___173_20402.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___173_20402.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20403 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20405 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20405 with
           | (univs1,binders,signature) ->
               let uu____20433 =
                 let uu____20442 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20442 with
                 | (univs_opening,univs2) ->
                     let uu____20469 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20469) in
               (match uu____20433 with
                | (univs_opening,univs_closing) ->
                    let uu____20486 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20492 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20493 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20492, uu____20493) in
                    (match uu____20486 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20515 =
                           match uu____20515 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20533 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20533 with
                                | (us1,t1) ->
                                    let uu____20544 =
                                      let uu____20549 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20556 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20549, uu____20556) in
                                    (match uu____20544 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20569 =
                                           let uu____20574 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20583 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20574, uu____20583) in
                                         (match uu____20569 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20599 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20599 in
                                              let uu____20600 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20600 with
                                               | (uu____20621,uu____20622,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20637 =
                                                       let uu____20638 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20638 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20637 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20643 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20643 with
                           | (uu____20656,uu____20657,t1) -> t1 in
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
                             | uu____20717 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20734 =
                               let uu____20735 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20735.FStar_Syntax_Syntax.n in
                             match uu____20734 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20794 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20823 =
                               let uu____20824 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20824.FStar_Syntax_Syntax.n in
                             match uu____20823 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20845) ->
                                 let uu____20866 = destruct_action_body body in
                                 (match uu____20866 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20911 ->
                                 let uu____20912 = destruct_action_body t in
                                 (match uu____20912 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20961 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20961 with
                           | (action_univs,t) ->
                               let uu____20970 = destruct_action_typ_templ t in
                               (match uu____20970 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___174_21011 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___174_21011.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___174_21011.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___175_21013 = ed in
                           let uu____21014 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____21015 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____21016 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21017 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21018 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21019 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21020 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21021 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21022 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21023 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21024 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21025 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21026 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21027 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___175_21013.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___175_21013.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____21014;
                             FStar_Syntax_Syntax.bind_wp = uu____21015;
                             FStar_Syntax_Syntax.if_then_else = uu____21016;
                             FStar_Syntax_Syntax.ite_wp = uu____21017;
                             FStar_Syntax_Syntax.stronger = uu____21018;
                             FStar_Syntax_Syntax.close_wp = uu____21019;
                             FStar_Syntax_Syntax.assert_p = uu____21020;
                             FStar_Syntax_Syntax.assume_p = uu____21021;
                             FStar_Syntax_Syntax.null_wp = uu____21022;
                             FStar_Syntax_Syntax.trivial = uu____21023;
                             FStar_Syntax_Syntax.repr = uu____21024;
                             FStar_Syntax_Syntax.return_repr = uu____21025;
                             FStar_Syntax_Syntax.bind_repr = uu____21026;
                             FStar_Syntax_Syntax.actions = uu____21027
                           } in
                         let uu___176_21030 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___176_21030.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___176_21030.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___176_21030.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___176_21030.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___87_21047 =
            match uu___87_21047 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21074 = elim_uvars_aux_t env us [] t in
                (match uu____21074 with
                 | (us1,uu____21098,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___177_21117 = sub_eff in
            let uu____21118 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21121 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___177_21117.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___177_21117.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21118;
              FStar_Syntax_Syntax.lift = uu____21121
            } in
          let uu___178_21124 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___178_21124.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___178_21124.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___178_21124.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___178_21124.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____21134 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21134 with
           | (univ_names1,binders1,comp1) ->
               let uu___179_21168 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___179_21168.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___179_21168.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___179_21168.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___179_21168.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21179 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t