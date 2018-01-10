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
  | Cfg of cfg
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____806 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____842 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____878 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____947 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____989 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1045 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1085 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1117 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1153 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1169 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1194 .
    'Auu____1194 ->
      FStar_Range.range -> 'Auu____1194 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1248 = FStar_ST.op_Bang r in
          match uu____1248 with
          | FStar_Pervasives_Native.Some uu____1325 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1408 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1408 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___72_1415  ->
    match uu___72_1415 with
    | Arg (c,uu____1417,uu____1418) ->
        let uu____1419 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1419
    | MemoLazy uu____1420 -> "MemoLazy"
    | Abs (uu____1427,bs,uu____1429,uu____1430,uu____1431) ->
        let uu____1436 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1436
    | UnivArgs uu____1441 -> "UnivArgs"
    | Match uu____1448 -> "Match"
    | App (uu____1455,t,uu____1457,uu____1458) ->
        let uu____1459 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1459
    | Meta (m,uu____1461) -> "Meta"
    | Let uu____1462 -> "Let"
    | Cfg uu____1471 -> "Cfg"
    | Debug (t,uu____1473) ->
        let uu____1474 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1474
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1482 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1482 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1498 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1498 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1511 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1511 then f () else ()
let is_empty: 'Auu____1515 . 'Auu____1515 Prims.list -> Prims.bool =
  fun uu___73_1521  ->
    match uu___73_1521 with | [] -> true | uu____1524 -> false
let lookup_bvar:
  'Auu____1531 'Auu____1532 .
    ('Auu____1532,'Auu____1531) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1531
  =
  fun env  ->
    fun x  ->
      try
        let uu____1556 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1556
      with
      | uu____1569 ->
          let uu____1570 =
            let uu____1571 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1571 in
          failwith uu____1570
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
          let uu____1608 =
            FStar_List.fold_left
              (fun uu____1634  ->
                 fun u1  ->
                   match uu____1634 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1659 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1659 with
                        | (k_u,n1) ->
                            let uu____1674 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1674
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1608 with
          | (uu____1692,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1717 =
                   let uu____1718 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1718 in
                 match uu____1717 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1736 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1745 ->
                   let uu____1746 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1746
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1752 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1761 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1770 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1777 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1777 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1794 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1794 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1802 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1810 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1810 with
                                  | (uu____1815,m) -> n1 <= m)) in
                        if uu____1802 then rest1 else us1
                    | uu____1820 -> us1)
               | uu____1825 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1829 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1829 in
        let uu____1832 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1832
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1834 = aux u in
           match uu____1834 with
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
          (fun uu____1938  ->
             let uu____1939 = FStar_Syntax_Print.tag_of_term t in
             let uu____1940 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1939
               uu____1940);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1947 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1949 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1974 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1975 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1976 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1977 ->
                  let uu____1994 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1994
                  then
                    let uu____1995 =
                      let uu____1996 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1997 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1996 uu____1997 in
                    failwith uu____1995
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2000 =
                    let uu____2001 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2001 in
                  mk uu____2000 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2008 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2008
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2010 = lookup_bvar env x in
                  (match uu____2010 with
                   | Univ uu____2013 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____2016,uu____2017) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2129 = closures_as_binders_delayed cfg env bs in
                  (match uu____2129 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2157 =
                         let uu____2158 =
                           let uu____2175 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2175) in
                         FStar_Syntax_Syntax.Tm_abs uu____2158 in
                       mk uu____2157 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2206 = closures_as_binders_delayed cfg env bs in
                  (match uu____2206 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2248 =
                    let uu____2259 =
                      let uu____2266 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2266] in
                    closures_as_binders_delayed cfg env uu____2259 in
                  (match uu____2248 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2284 =
                         let uu____2285 =
                           let uu____2292 =
                             let uu____2293 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2293
                               FStar_Pervasives_Native.fst in
                           (uu____2292, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2285 in
                       mk uu____2284 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2384 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2384
                    | FStar_Util.Inr c ->
                        let uu____2398 = close_comp cfg env c in
                        FStar_Util.Inr uu____2398 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2414 =
                    let uu____2415 =
                      let uu____2442 = closure_as_term_delayed cfg env t11 in
                      (uu____2442, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2415 in
                  mk uu____2414 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2493 =
                    let uu____2494 =
                      let uu____2501 = closure_as_term_delayed cfg env t' in
                      let uu____2504 =
                        let uu____2505 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2505 in
                      (uu____2501, uu____2504) in
                    FStar_Syntax_Syntax.Tm_meta uu____2494 in
                  mk uu____2493 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2565 =
                    let uu____2566 =
                      let uu____2573 = closure_as_term_delayed cfg env t' in
                      let uu____2576 =
                        let uu____2577 =
                          let uu____2584 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2584) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2577 in
                      (uu____2573, uu____2576) in
                    FStar_Syntax_Syntax.Tm_meta uu____2566 in
                  mk uu____2565 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2603 =
                    let uu____2604 =
                      let uu____2611 = closure_as_term_delayed cfg env t' in
                      let uu____2614 =
                        let uu____2615 =
                          let uu____2624 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2624) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2615 in
                      (uu____2611, uu____2614) in
                    FStar_Syntax_Syntax.Tm_meta uu____2604 in
                  mk uu____2603 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2637 =
                    let uu____2638 =
                      let uu____2645 = closure_as_term_delayed cfg env t' in
                      (uu____2645, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2638 in
                  mk uu____2637 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2685  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2704 =
                    let uu____2715 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2715
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2734 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___92_2746 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___92_2746.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___92_2746.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2734)) in
                  (match uu____2704 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___93_2762 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___93_2762.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___93_2762.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2773,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2832  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2857 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2857
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2877  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2899 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2899
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___94_2911 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___94_2911.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___94_2911.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___95_2912 = lb in
                    let uu____2913 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___95_2912.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___95_2912.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2913
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2943  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3032 =
                    match uu____3032 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3087 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3108 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3168  ->
                                        fun uu____3169  ->
                                          match (uu____3168, uu____3169) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3260 =
                                                norm_pat env3 p1 in
                                              (match uu____3260 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3108 with
                               | (pats1,env3) ->
                                   ((let uu___96_3342 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___96_3342.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___97_3361 = x in
                                let uu____3362 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___97_3361.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___97_3361.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3362
                                } in
                              ((let uu___98_3376 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___98_3376.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___99_3387 = x in
                                let uu____3388 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___99_3387.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___99_3387.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3388
                                } in
                              ((let uu___100_3402 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___100_3402.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___101_3418 = x in
                                let uu____3419 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___101_3418.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___101_3418.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3419
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___102_3426 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___102_3426.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3429 = norm_pat env1 pat in
                        (match uu____3429 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3458 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3458 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3464 =
                    let uu____3465 =
                      let uu____3488 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3488) in
                    FStar_Syntax_Syntax.Tm_match uu____3465 in
                  mk uu____3464 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3574 -> closure_as_term cfg env t
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
        | uu____3600 ->
            FStar_List.map
              (fun uu____3617  ->
                 match uu____3617 with
                 | (x,imp) ->
                     let uu____3636 = closure_as_term_delayed cfg env x in
                     (uu____3636, imp)) args
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
        let uu____3650 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3699  ->
                  fun uu____3700  ->
                    match (uu____3699, uu____3700) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___103_3770 = b in
                          let uu____3771 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___103_3770.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___103_3770.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3771
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3650 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3864 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3877 = closure_as_term_delayed cfg env t in
                 let uu____3878 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3877 uu____3878
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3891 = closure_as_term_delayed cfg env t in
                 let uu____3892 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3891 uu____3892
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
                        (fun uu___74_3918  ->
                           match uu___74_3918 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3922 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3922
                           | f -> f)) in
                 let uu____3926 =
                   let uu___104_3927 = c1 in
                   let uu____3928 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3928;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___104_3927.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3926)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___75_3938  ->
            match uu___75_3938 with
            | FStar_Syntax_Syntax.DECREASES uu____3939 -> false
            | uu____3942 -> true))
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
                   (fun uu___76_3960  ->
                      match uu___76_3960 with
                      | FStar_Syntax_Syntax.DECREASES uu____3961 -> false
                      | uu____3964 -> true)) in
            let rc1 =
              let uu___105_3966 = rc in
              let uu____3967 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___105_3966.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3967;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3974 -> lopt
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
    let uu____4064 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4064 in
  let arg_as_bounded_int uu____4092 =
    match uu____4092 with
    | (a,uu____4104) ->
        let uu____4111 =
          let uu____4112 = FStar_Syntax_Subst.compress a in
          uu____4112.FStar_Syntax_Syntax.n in
        (match uu____4111 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4122;
                FStar_Syntax_Syntax.vars = uu____4123;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4125;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4126;_},uu____4127)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4166 =
               let uu____4171 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4171) in
             FStar_Pervasives_Native.Some uu____4166
         | uu____4176 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4218 = f a in FStar_Pervasives_Native.Some uu____4218
    | uu____4219 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4269 = f a0 a1 in FStar_Pervasives_Native.Some uu____4269
    | uu____4270 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4319 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4319 in
  let binary_op as_a f res args =
    let uu____4375 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4375 in
  let as_primitive_step uu____4399 =
    match uu____4399 with
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
           let uu____4447 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4447) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4475 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4475) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4496 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4496) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4524 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4524) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4552 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4552) in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4669 =
          let uu____4678 = as_a a in
          let uu____4681 = as_b b in (uu____4678, uu____4681) in
        (match uu____4669 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4696 =
               let uu____4697 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4697 in
             FStar_Pervasives_Native.Some uu____4696
         | uu____4698 -> FStar_Pervasives_Native.None)
    | uu____4707 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4721 =
        let uu____4722 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4722 in
      mk uu____4721 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4732 =
      let uu____4735 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4735 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4732 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4767 =
      let uu____4768 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4768 in
    FStar_Syntax_Embeddings.embed_int rng uu____4767 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4786 = arg_as_string a1 in
        (match uu____4786 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4792 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4792 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4805 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4805
              | uu____4806 -> FStar_Pervasives_Native.None)
         | uu____4811 -> FStar_Pervasives_Native.None)
    | uu____4814 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4824 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4824 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4848 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4859 =
          let uu____4880 = arg_as_string fn in
          let uu____4883 = arg_as_int from_line in
          let uu____4886 = arg_as_int from_col in
          let uu____4889 = arg_as_int to_line in
          let uu____4892 = arg_as_int to_col in
          (uu____4880, uu____4883, uu____4886, uu____4889, uu____4892) in
        (match uu____4859 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4923 =
                 let uu____4924 = FStar_BigInt.to_int_fs from_l in
                 let uu____4925 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4924 uu____4925 in
               let uu____4926 =
                 let uu____4927 = FStar_BigInt.to_int_fs to_l in
                 let uu____4928 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4927 uu____4928 in
               FStar_Range.mk_range fn1 uu____4923 uu____4926 in
             let uu____4929 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4929
         | uu____4934 -> FStar_Pervasives_Native.None)
    | uu____4955 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4982)::(a1,uu____4984)::(a2,uu____4986)::[] ->
        let uu____5023 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5023 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5036 -> FStar_Pervasives_Native.None)
    | uu____5037 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5064)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5073 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5097 =
      let uu____5112 =
        let uu____5127 =
          let uu____5142 =
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
                                              let uu____5410 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5410,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5417 =
                                              let uu____5432 =
                                                let uu____5445 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5445,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5456 =
                                                let uu____5471 =
                                                  let uu____5486 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5486,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5495 =
                                                  let uu____5512 =
                                                    let uu____5527 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5527,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5536 =
                                                    let uu____5553 =
                                                      let uu____5572 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5572,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5553] in
                                                  uu____5512 :: uu____5536 in
                                                uu____5471 :: uu____5495 in
                                              uu____5432 :: uu____5456 in
                                            uu____5397 :: uu____5417 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5382 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5367 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5352 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5337 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5322 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5790 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5790 y)))
                                  :: uu____5307 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5292 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5277 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5262 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5247 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5232 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5936 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5936)))
                      :: uu____5217 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5962 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5962)))
                    :: uu____5202 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5988 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5988)))
                  :: uu____5187 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____6014 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____6014)))
                :: uu____5172 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5157 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5142 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5127 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5112 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5097 in
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
      let uu____6164 =
        let uu____6165 =
          let uu____6166 = FStar_Syntax_Syntax.as_arg c in [uu____6166] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6165 in
      uu____6164 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6201 =
              let uu____6214 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6214, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6234  ->
                        fun uu____6235  ->
                          match (uu____6234, uu____6235) with
                          | ((int_to_t1,x),(uu____6254,y)) ->
                              let uu____6264 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6264))) in
            let uu____6265 =
              let uu____6280 =
                let uu____6293 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6293, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6313  ->
                          fun uu____6314  ->
                            match (uu____6313, uu____6314) with
                            | ((int_to_t1,x),(uu____6333,y)) ->
                                let uu____6343 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6343))) in
              let uu____6344 =
                let uu____6359 =
                  let uu____6372 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6372, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6392  ->
                            fun uu____6393  ->
                              match (uu____6392, uu____6393) with
                              | ((int_to_t1,x),(uu____6412,y)) ->
                                  let uu____6422 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6422))) in
                [uu____6359] in
              uu____6280 :: uu____6344 in
            uu____6201 :: uu____6265)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6512)::(a1,uu____6514)::(a2,uu____6516)::[] ->
        let uu____6553 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6553 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6559 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6559.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6559.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6563 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6563.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6563.FStar_Syntax_Syntax.vars)
                })
         | uu____6564 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6566)::uu____6567::(a1,uu____6569)::(a2,uu____6571)::[] ->
        let uu____6620 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6620 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6626 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6626.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6626.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6630 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6630.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6630.FStar_Syntax_Syntax.vars)
                })
         | uu____6631 -> FStar_Pervasives_Native.None)
    | uu____6632 -> failwith "Unexpected number of arguments" in
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
      let uu____6651 =
        let uu____6652 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6652 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6651
    with | uu____6658 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6662 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6662) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6722  ->
           fun subst1  ->
             match uu____6722 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6763,uu____6764)) ->
                      let uu____6823 = b in
                      (match uu____6823 with
                       | (bv,uu____6831) ->
                           let uu____6832 =
                             let uu____6833 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6833 in
                           if uu____6832
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6838 = unembed_binder term1 in
                              match uu____6838 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6845 =
                                      let uu___110_6846 = bv in
                                      let uu____6847 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___110_6846.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___110_6846.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6847
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6845 in
                                  let b_for_x =
                                    let uu____6851 =
                                      let uu____6858 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6858) in
                                    FStar_Syntax_Syntax.NT uu____6851 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___77_6867  ->
                                         match uu___77_6867 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6868,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6870;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6871;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6876 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6877 -> subst1)) env []
let reduce_primops:
  'Auu____6894 'Auu____6895 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6895) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6894 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6936 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6936
          then tm
          else
            (let uu____6938 = FStar_Syntax_Util.head_and_args tm in
             match uu____6938 with
             | (head1,args) ->
                 let uu____6975 =
                   let uu____6976 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6976.FStar_Syntax_Syntax.n in
                 (match uu____6975 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6980 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6980 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6997  ->
                                   let uu____6998 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6999 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7006 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6998 uu____6999 uu____7006);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7011  ->
                                   let uu____7012 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7012);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7015  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7017 =
                                 prim_step.interpretation psc args in
                               match uu____7017 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7023  ->
                                         let uu____7024 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7024);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7030  ->
                                         let uu____7031 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7032 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7031 uu____7032);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7033 ->
                           (log_primops cfg
                              (fun uu____7037  ->
                                 let uu____7038 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7038);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7042  ->
                            let uu____7043 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7043);
                       (match args with
                        | (a1,uu____7045)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7062 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7074  ->
                            let uu____7075 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7075);
                       (match args with
                        | (t,uu____7077)::(r,uu____7079)::[] ->
                            let uu____7106 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7106 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___111_7110 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___111_7110.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___111_7110.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7113 -> tm))
                  | uu____7122 -> tm))
let reduce_equality:
  'Auu____7127 'Auu____7128 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7128) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7127 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___112_7166 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___112_7166.tcenv);
           delta_level = (uu___112_7166.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___112_7166.strong);
           memoize_lazy = (uu___112_7166.memoize_lazy)
         }) tm
let maybe_simplify_aux:
  'Auu____7173 'Auu____7174 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7174) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7173 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7216 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7216
          then tm1
          else
            (let w t =
               let uu___113_7228 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___113_7228.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___113_7228.FStar_Syntax_Syntax.vars)
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
               | uu____7245 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7250 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7250
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7271 =
                 match uu____7271 with
                 | (t1,q) ->
                     let uu____7284 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7284 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7312 -> (t1, q)) in
               let uu____7321 = FStar_Syntax_Util.head_and_args t in
               match uu____7321 with
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
                         FStar_Syntax_Syntax.pos = uu____7418;
                         FStar_Syntax_Syntax.vars = uu____7419;_},uu____7420);
                    FStar_Syntax_Syntax.pos = uu____7421;
                    FStar_Syntax_Syntax.vars = uu____7422;_},args)
                 ->
                 let uu____7448 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7448
                 then
                   let uu____7449 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7449 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7504)::
                        (uu____7505,(arg,uu____7507))::[] ->
                        maybe_auto_squash arg
                    | (uu____7572,(arg,uu____7574))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7575)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7640)::uu____7641::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7704::(FStar_Pervasives_Native.Some (false
                                   ),uu____7705)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7768 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7784 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7784
                    then
                      let uu____7785 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7785 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7840)::uu____7841::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7904::(FStar_Pervasives_Native.Some (true
                                     ),uu____7905)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7968)::
                          (uu____7969,(arg,uu____7971))::[] ->
                          maybe_auto_squash arg
                      | (uu____8036,(arg,uu____8038))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8039)::[]
                          -> maybe_auto_squash arg
                      | uu____8104 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8120 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8120
                       then
                         let uu____8121 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8121 with
                         | uu____8176::(FStar_Pervasives_Native.Some (true
                                        ),uu____8177)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8240)::uu____8241::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8304)::
                             (uu____8305,(arg,uu____8307))::[] ->
                             maybe_auto_squash arg
                         | (uu____8372,(p,uu____8374))::(uu____8375,(q,uu____8377))::[]
                             ->
                             let uu____8442 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8442
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8444 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8460 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8460
                          then
                            let uu____8461 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8461 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8516)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8555)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8594 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8610 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8610
                             then
                               match args with
                               | (t,uu____8612)::[] ->
                                   let uu____8629 =
                                     let uu____8630 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8630.FStar_Syntax_Syntax.n in
                                   (match uu____8629 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8633::[],body,uu____8635) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8662 -> tm1)
                                    | uu____8665 -> tm1)
                               | (uu____8666,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8667))::
                                   (t,uu____8669)::[] ->
                                   let uu____8708 =
                                     let uu____8709 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8709.FStar_Syntax_Syntax.n in
                                   (match uu____8708 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8712::[],body,uu____8714) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8741 -> tm1)
                                    | uu____8744 -> tm1)
                               | uu____8745 -> tm1
                             else
                               (let uu____8755 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8755
                                then
                                  match args with
                                  | (t,uu____8757)::[] ->
                                      let uu____8774 =
                                        let uu____8775 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8775.FStar_Syntax_Syntax.n in
                                      (match uu____8774 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8778::[],body,uu____8780)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8807 -> tm1)
                                       | uu____8810 -> tm1)
                                  | (uu____8811,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8812))::(t,uu____8814)::[] ->
                                      let uu____8853 =
                                        let uu____8854 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8854.FStar_Syntax_Syntax.n in
                                      (match uu____8853 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8857::[],body,uu____8859)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8886 -> tm1)
                                       | uu____8889 -> tm1)
                                  | uu____8890 -> tm1
                                else
                                  (let uu____8900 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8900
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8901;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8902;_},uu____8903)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8920;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8921;_},uu____8922)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8939 -> tm1
                                   else
                                     (let uu____8949 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8949 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8969 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8979;
                    FStar_Syntax_Syntax.vars = uu____8980;_},args)
                 ->
                 let uu____9002 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9002
                 then
                   let uu____9003 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9003 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9058)::
                        (uu____9059,(arg,uu____9061))::[] ->
                        maybe_auto_squash arg
                    | (uu____9126,(arg,uu____9128))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9129)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9194)::uu____9195::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9258::(FStar_Pervasives_Native.Some (false
                                   ),uu____9259)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9322 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9338 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9338
                    then
                      let uu____9339 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9339 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9394)::uu____9395::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9458::(FStar_Pervasives_Native.Some (true
                                     ),uu____9459)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9522)::
                          (uu____9523,(arg,uu____9525))::[] ->
                          maybe_auto_squash arg
                      | (uu____9590,(arg,uu____9592))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9593)::[]
                          -> maybe_auto_squash arg
                      | uu____9658 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9674 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9674
                       then
                         let uu____9675 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9675 with
                         | uu____9730::(FStar_Pervasives_Native.Some (true
                                        ),uu____9731)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9794)::uu____9795::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9858)::
                             (uu____9859,(arg,uu____9861))::[] ->
                             maybe_auto_squash arg
                         | (uu____9926,(p,uu____9928))::(uu____9929,(q,uu____9931))::[]
                             ->
                             let uu____9996 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9996
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9998 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10014 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10014
                          then
                            let uu____10015 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10015 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10070)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10109)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10148 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10164 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10164
                             then
                               match args with
                               | (t,uu____10166)::[] ->
                                   let uu____10183 =
                                     let uu____10184 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10184.FStar_Syntax_Syntax.n in
                                   (match uu____10183 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10187::[],body,uu____10189) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10216 -> tm1)
                                    | uu____10219 -> tm1)
                               | (uu____10220,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10221))::
                                   (t,uu____10223)::[] ->
                                   let uu____10262 =
                                     let uu____10263 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10263.FStar_Syntax_Syntax.n in
                                   (match uu____10262 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10266::[],body,uu____10268) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10295 -> tm1)
                                    | uu____10298 -> tm1)
                               | uu____10299 -> tm1
                             else
                               (let uu____10309 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10309
                                then
                                  match args with
                                  | (t,uu____10311)::[] ->
                                      let uu____10328 =
                                        let uu____10329 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10329.FStar_Syntax_Syntax.n in
                                      (match uu____10328 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10332::[],body,uu____10334)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10361 -> tm1)
                                       | uu____10364 -> tm1)
                                  | (uu____10365,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10366))::(t,uu____10368)::[] ->
                                      let uu____10407 =
                                        let uu____10408 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10408.FStar_Syntax_Syntax.n in
                                      (match uu____10407 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10411::[],body,uu____10413)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10440 -> tm1)
                                       | uu____10443 -> tm1)
                                  | uu____10444 -> tm1
                                else
                                  (let uu____10454 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10454
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10455;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10456;_},uu____10457)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10474;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10475;_},uu____10476)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10493 -> tm1
                                   else
                                     (let uu____10503 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10503 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10523 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10532 -> tm1)
let maybe_simplify:
  'Auu____10539 'Auu____10540 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10540) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10539 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10583 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10583
           then
             let uu____10584 = FStar_Syntax_Print.term_to_string tm in
             let uu____10585 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10584 uu____10585
           else ());
          tm'
let is_norm_request:
  'Auu____10591 .
    FStar_Syntax_Syntax.term -> 'Auu____10591 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10604 =
        let uu____10611 =
          let uu____10612 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10612.FStar_Syntax_Syntax.n in
        (uu____10611, args) in
      match uu____10604 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10618::uu____10619::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10623::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10628::uu____10629::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10632 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___78_10643  ->
    match uu___78_10643 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10649 =
          let uu____10652 =
            let uu____10653 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10653 in
          [uu____10652] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10649
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10668 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10668) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10706 =
          let uu____10709 =
            let uu____10714 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10714 s in
          FStar_All.pipe_right uu____10709 FStar_Util.must in
        FStar_All.pipe_right uu____10706 tr_norm_steps in
      match args with
      | uu____10739::(tm,uu____10741)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10764)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10779)::uu____10780::(tm,uu____10782)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10822 =
              let uu____10825 = full_norm steps in parse_steps uu____10825 in
            Beta :: uu____10822 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10834 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___79_10851  ->
    match uu___79_10851 with
    | (App
        (uu____10854,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10855;
                       FStar_Syntax_Syntax.vars = uu____10856;_},uu____10857,uu____10858))::uu____10859
        -> true
    | uu____10866 -> false
let firstn:
  'Auu____10872 .
    Prims.int ->
      'Auu____10872 Prims.list ->
        ('Auu____10872 Prims.list,'Auu____10872 Prims.list)
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
          (uu____10908,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10909;
                         FStar_Syntax_Syntax.vars = uu____10910;_},uu____10911,uu____10912))::uu____10913
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10920 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11067  ->
               let uu____11068 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11069 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11070 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11077 =
                 let uu____11078 =
                   let uu____11081 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11081 in
                 stack_to_string uu____11078 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11068 uu____11069 uu____11070 uu____11077);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11104 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11129 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11146 =
                 let uu____11147 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11148 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11147 uu____11148 in
               failwith uu____11146
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11149 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11166 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11167 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11168;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11169;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11172;
                 FStar_Syntax_Syntax.fv_delta = uu____11173;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11174;
                 FStar_Syntax_Syntax.fv_delta = uu____11175;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11176);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11184 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11184 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11190  ->
                     let uu____11191 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11192 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11191 uu____11192);
                if b
                then
                  (let uu____11193 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11193 t1 fv)
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
                 let uu___114_11232 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___114_11232.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_11232.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11265 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11265) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___115_11273 = cfg in
                 let uu____11274 =
                   FStar_List.filter
                     (fun uu___80_11277  ->
                        match uu___80_11277 with
                        | UnfoldOnly uu____11278 -> false
                        | NoDeltaSteps  -> false
                        | uu____11281 -> true) cfg.steps in
                 {
                   steps = uu____11274;
                   tcenv = (uu___115_11273.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___115_11273.primitive_steps);
                   strong = (uu___115_11273.strong);
                   memoize_lazy = (uu___115_11273.memoize_lazy)
                 } in
               let uu____11282 = get_norm_request (norm cfg' env []) args in
               (match uu____11282 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11298 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___81_11303  ->
                                match uu___81_11303 with
                                | UnfoldUntil uu____11304 -> true
                                | UnfoldOnly uu____11305 -> true
                                | uu____11308 -> false)) in
                      if uu____11298
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___116_11313 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___116_11313.tcenv);
                        delta_level;
                        primitive_steps = (uu___116_11313.primitive_steps);
                        strong = (uu___116_11313.strong);
                        memoize_lazy = (uu___116_11313.memoize_lazy)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11320 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11320
                      then
                        let uu____11323 =
                          let uu____11324 =
                            let uu____11329 = FStar_Util.now () in
                            (t1, uu____11329) in
                          Debug uu____11324 in
                        uu____11323 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11333 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11333
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11340 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11340
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11343 =
                      let uu____11350 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11350, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11343 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___82_11363  ->
                         match uu___82_11363 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11366 =
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
                 if uu____11366
                 then false
                 else
                   (let uu____11368 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___83_11375  ->
                              match uu___83_11375 with
                              | UnfoldOnly uu____11376 -> true
                              | uu____11379 -> false)) in
                    match uu____11368 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11383 -> should_delta) in
               (log cfg
                  (fun uu____11391  ->
                     let uu____11392 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11393 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11394 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11392 uu____11393 uu____11394);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11397 = lookup_bvar env x in
               (match uu____11397 with
                | Univ uu____11400 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11449 = FStar_ST.op_Bang r in
                      (match uu____11449 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11596  ->
                                 let uu____11597 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11598 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11597
                                   uu____11598);
                            (let uu____11599 =
                               let uu____11600 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11600.FStar_Syntax_Syntax.n in
                             match uu____11599 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11603 ->
                                 norm cfg env2 stack t'
                             | uu____11620 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11690)::uu____11691 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11700)::uu____11701 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11711,uu____11712))::stack_rest ->
                    (match c with
                     | Univ uu____11716 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11725 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11746  ->
                                    let uu____11747 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11747);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11787  ->
                                    let uu____11788 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11788);
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
                       (fun uu____11866  ->
                          let uu____11867 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11867);
                     norm cfg env stack1 t1)
                | (Debug uu____11868)::uu____11869 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11876 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11876
                    else
                      (let uu____11878 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11878 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11920  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11948 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11948
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11958 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11958)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_11963 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_11963.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_11963.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11964 -> lopt in
                           (log cfg
                              (fun uu____11970  ->
                                 let uu____11971 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11971);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_11980 = cfg in
                               {
                                 steps = (uu___118_11980.steps);
                                 tcenv = (uu___118_11980.tcenv);
                                 delta_level = (uu___118_11980.delta_level);
                                 primitive_steps =
                                   (uu___118_11980.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___118_11980.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11991)::uu____11992 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11999 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11999
                    else
                      (let uu____12001 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12001 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12043  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12071 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12071
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12081 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12081)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12086 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12086.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12086.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12087 -> lopt in
                           (log cfg
                              (fun uu____12093  ->
                                 let uu____12094 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12094);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12103 = cfg in
                               {
                                 steps = (uu___118_12103.steps);
                                 tcenv = (uu___118_12103.tcenv);
                                 delta_level = (uu___118_12103.delta_level);
                                 primitive_steps =
                                   (uu___118_12103.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___118_12103.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12114)::uu____12115 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12126 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12126
                    else
                      (let uu____12128 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12128 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12170  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12198 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12198
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12208 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12208)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12213 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12213.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12213.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12214 -> lopt in
                           (log cfg
                              (fun uu____12220  ->
                                 let uu____12221 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12221);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12230 = cfg in
                               {
                                 steps = (uu___118_12230.steps);
                                 tcenv = (uu___118_12230.tcenv);
                                 delta_level = (uu___118_12230.delta_level);
                                 primitive_steps =
                                   (uu___118_12230.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___118_12230.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12241)::uu____12242 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12253 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12253
                    else
                      (let uu____12255 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12255 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12297  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12325 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12325
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12335 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12335)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12340 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12340.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12340.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12341 -> lopt in
                           (log cfg
                              (fun uu____12347  ->
                                 let uu____12348 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12348);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12357 = cfg in
                               {
                                 steps = (uu___118_12357.steps);
                                 tcenv = (uu___118_12357.tcenv);
                                 delta_level = (uu___118_12357.delta_level);
                                 primitive_steps =
                                   (uu___118_12357.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___118_12357.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12368)::uu____12369 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12384 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12384
                    else
                      (let uu____12386 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12386 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12428  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12456 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12456
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12466 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12466)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12471 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12471.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12471.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12472 -> lopt in
                           (log cfg
                              (fun uu____12478  ->
                                 let uu____12479 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12479);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12488 = cfg in
                               {
                                 steps = (uu___118_12488.steps);
                                 tcenv = (uu___118_12488.tcenv);
                                 delta_level = (uu___118_12488.delta_level);
                                 primitive_steps =
                                   (uu___118_12488.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___118_12488.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12499 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12499
                    else
                      (let uu____12501 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12501 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12543  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12571 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12571
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12581 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12581)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12586 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12586.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12586.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12587 -> lopt in
                           (log cfg
                              (fun uu____12593  ->
                                 let uu____12594 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12594);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12603 = cfg in
                               {
                                 steps = (uu___118_12603.steps);
                                 tcenv = (uu___118_12603.tcenv);
                                 delta_level = (uu___118_12603.delta_level);
                                 primitive_steps =
                                   (uu___118_12603.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___118_12603.memoize_lazy)
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
                      (fun uu____12652  ->
                         fun stack1  ->
                           match uu____12652 with
                           | (a,aq) ->
                               let uu____12664 =
                                 let uu____12665 =
                                   let uu____12672 =
                                     let uu____12673 =
                                       let uu____12704 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12704, false) in
                                     Clos uu____12673 in
                                   (uu____12672, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12665 in
                               uu____12664 :: stack1) args) in
               (log cfg
                  (fun uu____12788  ->
                     let uu____12789 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12789);
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
                             ((let uu___119_12825 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___119_12825.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___119_12825.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12826 ->
                      let uu____12831 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12831)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12834 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12834 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12865 =
                          let uu____12866 =
                            let uu____12873 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___120_12875 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_12875.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_12875.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12873) in
                          FStar_Syntax_Syntax.Tm_refine uu____12866 in
                        mk uu____12865 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12894 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12894
               else
                 (let uu____12896 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12896 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12904 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12928  -> dummy :: env1) env) in
                        norm_comp cfg uu____12904 c1 in
                      let t2 =
                        let uu____12950 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12950 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13009)::uu____13010 ->
                    (log cfg
                       (fun uu____13021  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13022)::uu____13023 ->
                    (log cfg
                       (fun uu____13034  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13035,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13036;
                                   FStar_Syntax_Syntax.vars = uu____13037;_},uu____13038,uu____13039))::uu____13040
                    ->
                    (log cfg
                       (fun uu____13049  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13050)::uu____13051 ->
                    (log cfg
                       (fun uu____13062  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13063 ->
                    (log cfg
                       (fun uu____13066  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13070  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13087 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13087
                         | FStar_Util.Inr c ->
                             let uu____13095 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13095 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13108 =
                               let uu____13109 =
                                 let uu____13136 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13136, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13109 in
                             mk uu____13108 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13155 ->
                           let uu____13156 =
                             let uu____13157 =
                               let uu____13158 =
                                 let uu____13185 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13185, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13158 in
                             mk uu____13157 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13156))))
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
                         let uu____13295 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13295 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___121_13315 = cfg in
                               let uu____13316 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___121_13315.steps);
                                 tcenv = uu____13316;
                                 delta_level = (uu___121_13315.delta_level);
                                 primitive_steps =
                                   (uu___121_13315.primitive_steps);
                                 strong = (uu___121_13315.strong);
                                 memoize_lazy = (uu___121_13315.memoize_lazy)
                               } in
                             let norm1 t2 =
                               let uu____13321 =
                                 let uu____13322 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13322 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13321 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___122_13325 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___122_13325.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___122_13325.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13326 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13326
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13337,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13338;
                               FStar_Syntax_Syntax.lbunivs = uu____13339;
                               FStar_Syntax_Syntax.lbtyp = uu____13340;
                               FStar_Syntax_Syntax.lbeff = uu____13341;
                               FStar_Syntax_Syntax.lbdef = uu____13342;_}::uu____13343),uu____13344)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13380 =
                 (let uu____13383 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13383) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13385 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13385))) in
               if uu____13380
               then
                 let binder =
                   let uu____13387 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13387 in
                 let env1 =
                   let uu____13397 =
                     let uu____13404 =
                       let uu____13405 =
                         let uu____13436 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13436,
                           false) in
                       Clos uu____13405 in
                     ((FStar_Pervasives_Native.Some binder), uu____13404) in
                   uu____13397 :: env in
                 (log cfg
                    (fun uu____13529  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13531 =
                    let uu____13536 =
                      let uu____13537 =
                        let uu____13538 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13538
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13537] in
                    FStar_Syntax_Subst.open_term uu____13536 body in
                  match uu____13531 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13547  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13555 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13555 in
                          FStar_Util.Inl
                            (let uu___123_13565 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_13565.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_13565.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13568  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___124_13570 = lb in
                           let uu____13571 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___124_13570.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___124_13570.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13571
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13606  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___125_13629 = cfg in
                           {
                             steps = (uu___125_13629.steps);
                             tcenv = (uu___125_13629.tcenv);
                             delta_level = (uu___125_13629.delta_level);
                             primitive_steps =
                               (uu___125_13629.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___125_13629.memoize_lazy)
                           } in
                         log cfg1
                           (fun uu____13632  ->
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
               let uu____13649 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13649 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13685 =
                               let uu___126_13686 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___126_13686.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___126_13686.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13685 in
                           let uu____13687 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13687 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13713 =
                                   FStar_List.map (fun uu____13729  -> dummy)
                                     lbs1 in
                                 let uu____13730 =
                                   let uu____13739 =
                                     FStar_List.map
                                       (fun uu____13759  -> dummy) xs1 in
                                   FStar_List.append uu____13739 env in
                                 FStar_List.append uu____13713 uu____13730 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13783 =
                                       let uu___127_13784 = rc in
                                       let uu____13785 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___127_13784.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13785;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___127_13784.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13783
                                 | uu____13792 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___128_13796 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___128_13796.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___128_13796.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13806 =
                        FStar_List.map (fun uu____13822  -> dummy) lbs2 in
                      FStar_List.append uu____13806 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13830 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13830 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___129_13846 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___129_13846.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___129_13846.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13873 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13873
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13892 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13968  ->
                        match uu____13968 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___130_14089 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___130_14089.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___130_14089.FStar_Syntax_Syntax.sort)
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
               (match uu____13892 with
                | (rec_env,memos,uu____14302) ->
                    let uu____14355 =
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
                             let uu____14898 =
                               let uu____14905 =
                                 let uu____14906 =
                                   let uu____14937 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14937, false) in
                                 Clos uu____14906 in
                               (FStar_Pervasives_Native.None, uu____14905) in
                             uu____14898 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15047  ->
                     let uu____15048 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15048);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15070 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15072::uu____15073 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15078) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____15079 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____15110 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15124 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15124
                              | uu____15135 -> m in
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
              let uu____15147 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15147 in
            let uu____15148 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15148 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15161  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15172  ->
                      let uu____15173 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15174 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15173
                        uu____15174);
                 (let t1 =
                    let uu____15176 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15178 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15178) in
                    if uu____15176
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
                    | (UnivArgs (us',uu____15188))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15243 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15246 ->
                        let uu____15249 =
                          let uu____15250 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15250 in
                        failwith uu____15249
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
                let uu____15271 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15271
                then
                  let uu___131_15272 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___131_15272.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___131_15272.primitive_steps);
                    strong = (uu___131_15272.strong);
                    memoize_lazy = (uu___131_15272.memoize_lazy)
                  }
                else
                  (let uu___132_15274 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___132_15274.tcenv);
                     delta_level = (uu___132_15274.delta_level);
                     primitive_steps = (uu___132_15274.primitive_steps);
                     strong = (uu___132_15274.strong);
                     memoize_lazy = (uu___132_15274.memoize_lazy)
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
                  (fun uu____15303  ->
                     let uu____15304 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15305 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15304
                       uu____15305);
                (let uu____15306 =
                   let uu____15307 = FStar_Syntax_Subst.compress head2 in
                   uu____15307.FStar_Syntax_Syntax.n in
                 match uu____15306 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15325 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15325 with
                      | (uu____15326,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15332 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15340 =
                                   let uu____15341 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15341.FStar_Syntax_Syntax.n in
                                 match uu____15340 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15347,uu____15348))
                                     ->
                                     let uu____15357 =
                                       let uu____15358 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15358.FStar_Syntax_Syntax.n in
                                     (match uu____15357 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15364,msrc,uu____15366))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15375 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15375
                                      | uu____15376 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15377 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15378 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15378 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___133_15383 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___133_15383.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___133_15383.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___133_15383.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15384 = FStar_List.tl stack in
                                    let uu____15385 =
                                      let uu____15386 =
                                        let uu____15389 =
                                          let uu____15390 =
                                            let uu____15403 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15403) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15390 in
                                        FStar_Syntax_Syntax.mk uu____15389 in
                                      uu____15386
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15384 uu____15385
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15419 =
                                      let uu____15420 = is_return body in
                                      match uu____15420 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15424;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15425;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15430 -> false in
                                    if uu____15419
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
                                         let uu____15453 =
                                           let uu____15456 =
                                             let uu____15457 =
                                               let uu____15474 =
                                                 let uu____15477 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15477] in
                                               (uu____15474, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15457 in
                                           FStar_Syntax_Syntax.mk uu____15456 in
                                         uu____15453
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15493 =
                                           let uu____15494 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15494.FStar_Syntax_Syntax.n in
                                         match uu____15493 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15500::uu____15501::[])
                                             ->
                                             let uu____15508 =
                                               let uu____15511 =
                                                 let uu____15512 =
                                                   let uu____15519 =
                                                     let uu____15522 =
                                                       let uu____15523 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15523 in
                                                     let uu____15524 =
                                                       let uu____15527 =
                                                         let uu____15528 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15528 in
                                                       [uu____15527] in
                                                     uu____15522 ::
                                                       uu____15524 in
                                                   (bind1, uu____15519) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15512 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15511 in
                                             uu____15508
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15536 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15542 =
                                           let uu____15545 =
                                             let uu____15546 =
                                               let uu____15561 =
                                                 let uu____15564 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15565 =
                                                   let uu____15568 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15569 =
                                                     let uu____15572 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15573 =
                                                       let uu____15576 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15577 =
                                                         let uu____15580 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15581 =
                                                           let uu____15584 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15584] in
                                                         uu____15580 ::
                                                           uu____15581 in
                                                       uu____15576 ::
                                                         uu____15577 in
                                                     uu____15572 ::
                                                       uu____15573 in
                                                   uu____15568 :: uu____15569 in
                                                 uu____15564 :: uu____15565 in
                                               (bind_inst, uu____15561) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15546 in
                                           FStar_Syntax_Syntax.mk uu____15545 in
                                         uu____15542
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15595  ->
                                            let uu____15596 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15596);
                                       (let uu____15597 = FStar_List.tl stack in
                                        norm cfg env uu____15597 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15621 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15621 with
                      | (uu____15622,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15657 =
                                  let uu____15658 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15658.FStar_Syntax_Syntax.n in
                                match uu____15657 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15664) -> t2
                                | uu____15669 -> head3 in
                              let uu____15670 =
                                let uu____15671 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15671.FStar_Syntax_Syntax.n in
                              match uu____15670 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15677 -> FStar_Pervasives_Native.None in
                            let uu____15678 = maybe_extract_fv head3 in
                            match uu____15678 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15688 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15688
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15693 = maybe_extract_fv head4 in
                                  match uu____15693 with
                                  | FStar_Pervasives_Native.Some uu____15698
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15699 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15704 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15719 =
                              match uu____15719 with
                              | (e,q) ->
                                  let uu____15726 =
                                    let uu____15727 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15727.FStar_Syntax_Syntax.n in
                                  (match uu____15726 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15742 -> false) in
                            let uu____15743 =
                              let uu____15744 =
                                let uu____15751 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15751 :: args in
                              FStar_Util.for_some is_arg_impure uu____15744 in
                            if uu____15743
                            then
                              let uu____15756 =
                                let uu____15757 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15757 in
                              failwith uu____15756
                            else ());
                           (let uu____15759 = maybe_unfold_action head_app in
                            match uu____15759 with
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
                                let uu____15796 = FStar_List.tl stack in
                                norm cfg env uu____15796 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15798) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15822 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15822 in
                     (log cfg
                        (fun uu____15826  ->
                           let uu____15827 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15827);
                      (let uu____15828 = FStar_List.tl stack in
                       norm cfg env uu____15828 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15830) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15955  ->
                               match uu____15955 with
                               | (pat,wopt,tm) ->
                                   let uu____16003 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____16003))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____16035 = FStar_List.tl stack in
                     norm cfg env uu____16035 tm
                 | uu____16036 -> fallback ())
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
              (fun uu____16050  ->
                 let uu____16051 = FStar_Ident.string_of_lid msrc in
                 let uu____16052 = FStar_Ident.string_of_lid mtgt in
                 let uu____16053 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16051
                   uu____16052 uu____16053);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____16055 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____16055 with
               | (uu____16056,return_repr) ->
                   let return_inst =
                     let uu____16065 =
                       let uu____16066 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____16066.FStar_Syntax_Syntax.n in
                     match uu____16065 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16072::[]) ->
                         let uu____16079 =
                           let uu____16082 =
                             let uu____16083 =
                               let uu____16090 =
                                 let uu____16093 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____16093] in
                               (return_tm, uu____16090) in
                             FStar_Syntax_Syntax.Tm_uinst uu____16083 in
                           FStar_Syntax_Syntax.mk uu____16082 in
                         uu____16079 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16101 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____16104 =
                     let uu____16107 =
                       let uu____16108 =
                         let uu____16123 =
                           let uu____16126 = FStar_Syntax_Syntax.as_arg t in
                           let uu____16127 =
                             let uu____16130 = FStar_Syntax_Syntax.as_arg e in
                             [uu____16130] in
                           uu____16126 :: uu____16127 in
                         (return_inst, uu____16123) in
                       FStar_Syntax_Syntax.Tm_app uu____16108 in
                     FStar_Syntax_Syntax.mk uu____16107 in
                   uu____16104 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16139 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16139 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16142 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16142
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16143;
                     FStar_TypeChecker_Env.mtarget = uu____16144;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16145;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16160;
                     FStar_TypeChecker_Env.mtarget = uu____16161;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16162;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16186 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16187 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16186 t FStar_Syntax_Syntax.tun uu____16187)
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
                (fun uu____16243  ->
                   match uu____16243 with
                   | (a,imp) ->
                       let uu____16254 = norm cfg env [] a in
                       (uu____16254, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___134_16268 = comp in
            let uu____16269 =
              let uu____16270 =
                let uu____16279 = norm cfg env [] t in
                let uu____16280 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16279, uu____16280) in
              FStar_Syntax_Syntax.Total uu____16270 in
            {
              FStar_Syntax_Syntax.n = uu____16269;
              FStar_Syntax_Syntax.pos =
                (uu___134_16268.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___134_16268.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___135_16295 = comp in
            let uu____16296 =
              let uu____16297 =
                let uu____16306 = norm cfg env [] t in
                let uu____16307 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16306, uu____16307) in
              FStar_Syntax_Syntax.GTotal uu____16297 in
            {
              FStar_Syntax_Syntax.n = uu____16296;
              FStar_Syntax_Syntax.pos =
                (uu___135_16295.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_16295.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16359  ->
                      match uu____16359 with
                      | (a,i) ->
                          let uu____16370 = norm cfg env [] a in
                          (uu____16370, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___84_16381  ->
                      match uu___84_16381 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16385 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16385
                      | f -> f)) in
            let uu___136_16389 = comp in
            let uu____16390 =
              let uu____16391 =
                let uu___137_16392 = ct in
                let uu____16393 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16394 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16397 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16393;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___137_16392.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16394;
                  FStar_Syntax_Syntax.effect_args = uu____16397;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16391 in
            {
              FStar_Syntax_Syntax.n = uu____16390;
              FStar_Syntax_Syntax.pos =
                (uu___136_16389.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16389.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16408  ->
        match uu____16408 with
        | (x,imp) ->
            let uu____16411 =
              let uu___138_16412 = x in
              let uu____16413 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___138_16412.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___138_16412.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16413
              } in
            (uu____16411, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16419 =
          FStar_List.fold_left
            (fun uu____16437  ->
               fun b  ->
                 match uu____16437 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16419 with | (nbs,uu____16477) -> FStar_List.rev nbs
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
            let uu____16493 =
              let uu___139_16494 = rc in
              let uu____16495 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___139_16494.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16495;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___139_16494.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16493
        | uu____16502 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16515  ->
               let uu____16516 = FStar_Syntax_Print.tag_of_term t in
               let uu____16517 = FStar_Syntax_Print.term_to_string t in
               let uu____16518 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16525 =
                 let uu____16526 =
                   let uu____16529 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16529 in
                 stack_to_string uu____16526 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16516 uu____16517 uu____16518 uu____16525);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16558 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16558
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16560 =
                     let uu____16561 =
                       let uu____16562 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16562 in
                     FStar_Util.string_of_int uu____16561 in
                   let uu____16567 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16568 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16560 uu____16567 uu____16568
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16622  ->
                     let uu____16623 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16623);
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
               let uu____16659 =
                 let uu___140_16660 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___140_16660.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___140_16660.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16659
           | (Arg (Univ uu____16661,uu____16662,uu____16663))::uu____16664 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16667,uu____16668))::uu____16669 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16685),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16738  ->
                     let uu____16739 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16739);
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
                  (let uu____16749 = FStar_ST.op_Bang m in
                   match uu____16749 with
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
                   | FStar_Pervasives_Native.Some (uu____16915,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16962 =
                 log cfg
                   (fun uu____16966  ->
                      let uu____16967 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16967);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16971 =
                 let uu____16972 = FStar_Syntax_Subst.compress t in
                 uu____16972.FStar_Syntax_Syntax.n in
               (match uu____16971 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16999 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16999 in
                    (log cfg
                       (fun uu____17003  ->
                          let uu____17004 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____17004);
                     (let uu____17005 = FStar_List.tl stack in
                      norm cfg env1 uu____17005 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____17006);
                       FStar_Syntax_Syntax.pos = uu____17007;
                       FStar_Syntax_Syntax.vars = uu____17008;_},(e,uu____17010)::[])
                    -> norm cfg env1 stack' e
                | uu____17039 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17050 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17050
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17062  ->
                     let uu____17063 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17063);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17068 =
                   log cfg
                     (fun uu____17073  ->
                        let uu____17074 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17075 =
                          let uu____17076 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17093  ->
                                    match uu____17093 with
                                    | (p,uu____17103,uu____17104) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17076
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17074 uu____17075);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___85_17121  ->
                                match uu___85_17121 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17122 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___141_17126 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___141_17126.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___141_17126.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___141_17126.memoize_lazy)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17158 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17179 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17239  ->
                                    fun uu____17240  ->
                                      match (uu____17239, uu____17240) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17331 = norm_pat env3 p1 in
                                          (match uu____17331 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17179 with
                           | (pats1,env3) ->
                               ((let uu___142_17413 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___142_17413.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___143_17432 = x in
                            let uu____17433 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___143_17432.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___143_17432.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17433
                            } in
                          ((let uu___144_17447 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___144_17447.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___145_17458 = x in
                            let uu____17459 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___145_17458.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___145_17458.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17459
                            } in
                          ((let uu___146_17473 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___146_17473.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___147_17489 = x in
                            let uu____17490 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_17489.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_17489.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17490
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___148_17497 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___148_17497.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17507 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17521 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17521 with
                                  | (p,wopt,e) ->
                                      let uu____17541 = norm_pat env1 p in
                                      (match uu____17541 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17566 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17566 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17572 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17572) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17582) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17587 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17588;
                         FStar_Syntax_Syntax.fv_delta = uu____17589;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17590;
                         FStar_Syntax_Syntax.fv_delta = uu____17591;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17592);_}
                       -> true
                   | uu____17599 -> false in
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
                   let uu____17744 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17744 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17831 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17870 ->
                                 let uu____17871 =
                                   let uu____17872 = is_cons head1 in
                                   Prims.op_Negation uu____17872 in
                                 FStar_Util.Inr uu____17871)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17897 =
                              let uu____17898 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17898.FStar_Syntax_Syntax.n in
                            (match uu____17897 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17916 ->
                                 let uu____17917 =
                                   let uu____17918 = is_cons head1 in
                                   Prims.op_Negation uu____17918 in
                                 FStar_Util.Inr uu____17917))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17987)::rest_a,(p1,uu____17990)::rest_p) ->
                       let uu____18034 = matches_pat t1 p1 in
                       (match uu____18034 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18083 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18189 = matches_pat scrutinee1 p1 in
                       (match uu____18189 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18229  ->
                                  let uu____18230 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18231 =
                                    let uu____18232 =
                                      FStar_List.map
                                        (fun uu____18242  ->
                                           match uu____18242 with
                                           | (uu____18247,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18232
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18230 uu____18231);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18278  ->
                                       match uu____18278 with
                                       | (bv,t1) ->
                                           let uu____18301 =
                                             let uu____18308 =
                                               let uu____18311 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18311 in
                                             let uu____18312 =
                                               let uu____18313 =
                                                 let uu____18344 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18344, false) in
                                               Clos uu____18313 in
                                             (uu____18308, uu____18312) in
                                           uu____18301 :: env2) env1 s in
                              let uu____18461 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18461))) in
                 let uu____18462 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18462
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___86_18483  ->
                match uu___86_18483 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18487 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18493 -> d in
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
            let uu___149_18518 = config s e in
            {
              steps = (uu___149_18518.steps);
              tcenv = (uu___149_18518.tcenv);
              delta_level = (uu___149_18518.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___149_18518.strong);
              memoize_lazy = (uu___149_18518.memoize_lazy)
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
      fun t  -> let uu____18543 = config s e in norm_comp uu____18543 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18556 = config [] env in norm_universe uu____18556 [] u
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
        let uu____18574 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18574 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18581 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___150_18600 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___150_18600.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___150_18600.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18607 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18607
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
                  let uu___151_18616 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___151_18616.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___151_18616.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___151_18616.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___152_18618 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18618.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18618.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18618.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___152_18618.FStar_Syntax_Syntax.flags)
                  } in
            let uu___153_18619 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___153_18619.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___153_18619.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18621 -> c
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
        let uu____18633 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18633 in
      let uu____18640 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18640
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18644  ->
                 let uu____18645 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18645)
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
            ((let uu____18662 =
                let uu____18667 =
                  let uu____18668 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18668 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18667) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18662);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18679 = config [AllowUnboundUniverses] env in
          norm_comp uu____18679 [] c
        with
        | e ->
            ((let uu____18692 =
                let uu____18697 =
                  let uu____18698 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18698 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18697) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18692);
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
                   let uu____18735 =
                     let uu____18736 =
                       let uu____18743 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18743) in
                     FStar_Syntax_Syntax.Tm_refine uu____18736 in
                   mk uu____18735 t01.FStar_Syntax_Syntax.pos
               | uu____18748 -> t2)
          | uu____18749 -> t2 in
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
        let uu____18789 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18789 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18818 ->
                 let uu____18825 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18825 with
                  | (actuals,uu____18835,uu____18836) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18850 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18850 with
                         | (binders,args) ->
                             let uu____18867 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18867
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
      | uu____18875 ->
          let uu____18876 = FStar_Syntax_Util.head_and_args t in
          (match uu____18876 with
           | (head1,args) ->
               let uu____18913 =
                 let uu____18914 = FStar_Syntax_Subst.compress head1 in
                 uu____18914.FStar_Syntax_Syntax.n in
               (match uu____18913 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18917,thead) ->
                    let uu____18943 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18943 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18985 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___158_18993 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___158_18993.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___158_18993.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___158_18993.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___158_18993.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___158_18993.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___158_18993.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___158_18993.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___158_18993.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___158_18993.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___158_18993.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___158_18993.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___158_18993.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___158_18993.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___158_18993.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___158_18993.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___158_18993.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___158_18993.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___158_18993.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___158_18993.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___158_18993.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___158_18993.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___158_18993.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___158_18993.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___158_18993.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___158_18993.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___158_18993.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___158_18993.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___158_18993.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___158_18993.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___158_18993.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___158_18993.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18985 with
                            | (uu____18994,ty,uu____18996) ->
                                eta_expand_with_type env t ty))
                | uu____18997 ->
                    let uu____18998 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___159_19006 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___159_19006.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___159_19006.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___159_19006.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___159_19006.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___159_19006.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___159_19006.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___159_19006.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___159_19006.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___159_19006.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___159_19006.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___159_19006.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___159_19006.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___159_19006.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___159_19006.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___159_19006.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___159_19006.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___159_19006.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___159_19006.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___159_19006.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___159_19006.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___159_19006.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___159_19006.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___159_19006.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___159_19006.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___159_19006.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___159_19006.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___159_19006.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___159_19006.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___159_19006.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___159_19006.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___159_19006.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18998 with
                     | (uu____19007,ty,uu____19009) ->
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
            | (uu____19083,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19089,FStar_Util.Inl t) ->
                let uu____19095 =
                  let uu____19098 =
                    let uu____19099 =
                      let uu____19112 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19112) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19099 in
                  FStar_Syntax_Syntax.mk uu____19098 in
                uu____19095 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19116 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19116 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19143 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19198 ->
                    let uu____19199 =
                      let uu____19208 =
                        let uu____19209 = FStar_Syntax_Subst.compress t3 in
                        uu____19209.FStar_Syntax_Syntax.n in
                      (uu____19208, tc) in
                    (match uu____19199 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19234) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19271) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19310,FStar_Util.Inl uu____19311) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19334 -> failwith "Impossible") in
              (match uu____19143 with
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
          let uu____19439 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19439 with
          | (univ_names1,binders1,tc) ->
              let uu____19497 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19497)
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
          let uu____19532 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19532 with
          | (univ_names1,binders1,tc) ->
              let uu____19592 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19592)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19625 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19625 with
           | (univ_names1,binders1,typ1) ->
               let uu___160_19653 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___160_19653.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___160_19653.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___160_19653.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___160_19653.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___161_19674 = s in
          let uu____19675 =
            let uu____19676 =
              let uu____19685 = FStar_List.map (elim_uvars env) sigs in
              (uu____19685, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19676 in
          {
            FStar_Syntax_Syntax.sigel = uu____19675;
            FStar_Syntax_Syntax.sigrng =
              (uu___161_19674.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___161_19674.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___161_19674.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___161_19674.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19702 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19702 with
           | (univ_names1,uu____19720,typ1) ->
               let uu___162_19734 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___162_19734.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___162_19734.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___162_19734.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___162_19734.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19740 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19740 with
           | (univ_names1,uu____19758,typ1) ->
               let uu___163_19772 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19772.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19772.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19772.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19772.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19806 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19806 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19829 =
                            let uu____19830 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19830 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19829 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___164_19833 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___164_19833.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___164_19833.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___165_19834 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___165_19834.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___165_19834.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___165_19834.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___165_19834.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___166_19846 = s in
          let uu____19847 =
            let uu____19848 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19848 in
          {
            FStar_Syntax_Syntax.sigel = uu____19847;
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19846.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19846.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19846.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19846.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19852 = elim_uvars_aux_t env us [] t in
          (match uu____19852 with
           | (us1,uu____19870,t1) ->
               let uu___167_19884 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___167_19884.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___167_19884.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___167_19884.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___167_19884.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19885 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19887 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19887 with
           | (univs1,binders,signature) ->
               let uu____19915 =
                 let uu____19924 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19924 with
                 | (univs_opening,univs2) ->
                     let uu____19951 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19951) in
               (match uu____19915 with
                | (univs_opening,univs_closing) ->
                    let uu____19968 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19974 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19975 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19974, uu____19975) in
                    (match uu____19968 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19997 =
                           match uu____19997 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20015 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20015 with
                                | (us1,t1) ->
                                    let uu____20026 =
                                      let uu____20031 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20038 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20031, uu____20038) in
                                    (match uu____20026 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20051 =
                                           let uu____20056 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20065 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20056, uu____20065) in
                                         (match uu____20051 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20081 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20081 in
                                              let uu____20082 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20082 with
                                               | (uu____20103,uu____20104,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20119 =
                                                       let uu____20120 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20120 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20119 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20125 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20125 with
                           | (uu____20138,uu____20139,t1) -> t1 in
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
                             | uu____20199 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20216 =
                               let uu____20217 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20217.FStar_Syntax_Syntax.n in
                             match uu____20216 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20276 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20305 =
                               let uu____20306 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20306.FStar_Syntax_Syntax.n in
                             match uu____20305 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20327) ->
                                 let uu____20348 = destruct_action_body body in
                                 (match uu____20348 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20393 ->
                                 let uu____20394 = destruct_action_body t in
                                 (match uu____20394 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20443 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20443 with
                           | (action_univs,t) ->
                               let uu____20452 = destruct_action_typ_templ t in
                               (match uu____20452 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___168_20493 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___168_20493.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___168_20493.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___169_20495 = ed in
                           let uu____20496 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20497 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20498 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20499 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20500 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20501 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20502 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20503 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20504 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20505 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20506 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20507 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20508 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20509 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___169_20495.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___169_20495.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20496;
                             FStar_Syntax_Syntax.bind_wp = uu____20497;
                             FStar_Syntax_Syntax.if_then_else = uu____20498;
                             FStar_Syntax_Syntax.ite_wp = uu____20499;
                             FStar_Syntax_Syntax.stronger = uu____20500;
                             FStar_Syntax_Syntax.close_wp = uu____20501;
                             FStar_Syntax_Syntax.assert_p = uu____20502;
                             FStar_Syntax_Syntax.assume_p = uu____20503;
                             FStar_Syntax_Syntax.null_wp = uu____20504;
                             FStar_Syntax_Syntax.trivial = uu____20505;
                             FStar_Syntax_Syntax.repr = uu____20506;
                             FStar_Syntax_Syntax.return_repr = uu____20507;
                             FStar_Syntax_Syntax.bind_repr = uu____20508;
                             FStar_Syntax_Syntax.actions = uu____20509
                           } in
                         let uu___170_20512 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___170_20512.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___170_20512.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___170_20512.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___170_20512.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___87_20529 =
            match uu___87_20529 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20556 = elim_uvars_aux_t env us [] t in
                (match uu____20556 with
                 | (us1,uu____20580,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___171_20599 = sub_eff in
            let uu____20600 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20603 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___171_20599.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___171_20599.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20600;
              FStar_Syntax_Syntax.lift = uu____20603
            } in
          let uu___172_20606 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___172_20606.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___172_20606.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___172_20606.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___172_20606.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20616 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20616 with
           | (univ_names1,binders1,comp1) ->
               let uu___173_20650 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___173_20650.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___173_20650.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___173_20650.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___173_20650.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20661 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t