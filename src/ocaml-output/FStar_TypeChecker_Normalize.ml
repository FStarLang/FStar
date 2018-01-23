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
          | FStar_Pervasives_Native.Some uu____1296 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1350 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1350 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___73_1357  ->
    match uu___73_1357 with
    | Arg (c,uu____1359,uu____1360) ->
        let uu____1361 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1361
    | MemoLazy uu____1362 -> "MemoLazy"
    | Abs (uu____1369,bs,uu____1371,uu____1372,uu____1373) ->
        let uu____1378 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1378
    | UnivArgs uu____1383 -> "UnivArgs"
    | Match uu____1390 -> "Match"
    | App (uu____1397,t,uu____1399,uu____1400) ->
        let uu____1401 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1401
    | Meta (m,uu____1403) -> "Meta"
    | Let uu____1404 -> "Let"
    | Cfg uu____1413 -> "Cfg"
    | Debug (t,uu____1415) ->
        let uu____1416 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1416
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1424 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1424 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1440 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1440 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1453 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1453 then f () else ()
let is_empty: 'Auu____1457 . 'Auu____1457 Prims.list -> Prims.bool =
  fun uu___74_1463  ->
    match uu___74_1463 with | [] -> true | uu____1466 -> false
let lookup_bvar:
  'Auu____1473 'Auu____1474 .
    ('Auu____1474,'Auu____1473) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1473
  =
  fun env  ->
    fun x  ->
      try
        let uu____1498 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1498
      with
      | uu____1511 ->
          let uu____1512 =
            let uu____1513 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1513 in
          failwith uu____1512
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
          let uu____1550 =
            FStar_List.fold_left
              (fun uu____1576  ->
                 fun u1  ->
                   match uu____1576 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1601 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1601 with
                        | (k_u,n1) ->
                            let uu____1616 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1616
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1550 with
          | (uu____1634,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1659 =
                   let uu____1660 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1660 in
                 match uu____1659 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1678 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1687 ->
                   let uu____1688 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1688
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1694 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1703 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1712 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1719 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1719 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1736 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1736 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1744 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1752 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1752 with
                                  | (uu____1757,m) -> n1 <= m)) in
                        if uu____1744 then rest1 else us1
                    | uu____1762 -> us1)
               | uu____1767 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1771 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1771 in
        let uu____1774 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1774
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1776 = aux u in
           match uu____1776 with
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
          (fun uu____1880  ->
             let uu____1881 = FStar_Syntax_Print.tag_of_term t in
             let uu____1882 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1881
               uu____1882);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1889 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1891 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1916 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1917 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1918 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1919 ->
                  let uu____1936 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1936
                  then
                    let uu____1937 =
                      let uu____1938 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1939 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1938 uu____1939 in
                    failwith uu____1937
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1942 =
                    let uu____1943 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1943 in
                  mk uu____1942 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1950 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1950
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1952 = lookup_bvar env x in
                  (match uu____1952 with
                   | Univ uu____1955 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1958,uu____1959) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2071 = closures_as_binders_delayed cfg env bs in
                  (match uu____2071 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2099 =
                         let uu____2100 =
                           let uu____2117 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2117) in
                         FStar_Syntax_Syntax.Tm_abs uu____2100 in
                       mk uu____2099 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2148 = closures_as_binders_delayed cfg env bs in
                  (match uu____2148 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2190 =
                    let uu____2201 =
                      let uu____2208 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2208] in
                    closures_as_binders_delayed cfg env uu____2201 in
                  (match uu____2190 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2226 =
                         let uu____2227 =
                           let uu____2234 =
                             let uu____2235 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2235
                               FStar_Pervasives_Native.fst in
                           (uu____2234, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2227 in
                       mk uu____2226 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2326 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2326
                    | FStar_Util.Inr c ->
                        let uu____2340 = close_comp cfg env c in
                        FStar_Util.Inr uu____2340 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2356 =
                    let uu____2357 =
                      let uu____2384 = closure_as_term_delayed cfg env t11 in
                      (uu____2384, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2357 in
                  mk uu____2356 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2435 =
                    let uu____2436 =
                      let uu____2443 = closure_as_term_delayed cfg env t' in
                      let uu____2446 =
                        let uu____2447 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2447 in
                      (uu____2443, uu____2446) in
                    FStar_Syntax_Syntax.Tm_meta uu____2436 in
                  mk uu____2435 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2507 =
                    let uu____2508 =
                      let uu____2515 = closure_as_term_delayed cfg env t' in
                      let uu____2518 =
                        let uu____2519 =
                          let uu____2526 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2526) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2519 in
                      (uu____2515, uu____2518) in
                    FStar_Syntax_Syntax.Tm_meta uu____2508 in
                  mk uu____2507 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2545 =
                    let uu____2546 =
                      let uu____2553 = closure_as_term_delayed cfg env t' in
                      let uu____2556 =
                        let uu____2557 =
                          let uu____2566 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2566) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2557 in
                      (uu____2553, uu____2556) in
                    FStar_Syntax_Syntax.Tm_meta uu____2546 in
                  mk uu____2545 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2579 =
                    let uu____2580 =
                      let uu____2587 = closure_as_term_delayed cfg env t' in
                      (uu____2587, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2580 in
                  mk uu____2579 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2627  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2646 =
                    let uu____2657 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2657
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2676 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___93_2688 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_2688.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_2688.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2676)) in
                  (match uu____2646 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___94_2704 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_2704.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_2704.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2715,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2774  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2799 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2799
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2819  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2841 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2841
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___95_2853 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___95_2853.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___95_2853.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___96_2854 = lb in
                    let uu____2855 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___96_2854.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___96_2854.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2855
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2885  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2974 =
                    match uu____2974 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3029 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3050 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3110  ->
                                        fun uu____3111  ->
                                          match (uu____3110, uu____3111) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3202 =
                                                norm_pat env3 p1 in
                                              (match uu____3202 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3050 with
                               | (pats1,env3) ->
                                   ((let uu___97_3284 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___97_3284.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___98_3303 = x in
                                let uu____3304 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___98_3303.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_3303.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3304
                                } in
                              ((let uu___99_3318 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___99_3318.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___100_3329 = x in
                                let uu____3330 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___100_3329.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___100_3329.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3330
                                } in
                              ((let uu___101_3344 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___101_3344.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___102_3360 = x in
                                let uu____3361 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3360.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3360.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3361
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___103_3368 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3368.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3371 = norm_pat env1 pat in
                        (match uu____3371 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3400 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3400 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3406 =
                    let uu____3407 =
                      let uu____3430 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3430) in
                    FStar_Syntax_Syntax.Tm_match uu____3407 in
                  mk uu____3406 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3516 -> closure_as_term cfg env t
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
        | uu____3542 ->
            FStar_List.map
              (fun uu____3559  ->
                 match uu____3559 with
                 | (x,imp) ->
                     let uu____3578 = closure_as_term_delayed cfg env x in
                     (uu____3578, imp)) args
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
        let uu____3592 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3641  ->
                  fun uu____3642  ->
                    match (uu____3641, uu____3642) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___104_3712 = b in
                          let uu____3713 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___104_3712.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___104_3712.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3713
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3592 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3806 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3819 = closure_as_term_delayed cfg env t in
                 let uu____3820 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3819 uu____3820
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3833 = closure_as_term_delayed cfg env t in
                 let uu____3834 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3833 uu____3834
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
                        (fun uu___75_3860  ->
                           match uu___75_3860 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3864 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3864
                           | f -> f)) in
                 let uu____3868 =
                   let uu___105_3869 = c1 in
                   let uu____3870 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3870;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___105_3869.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3868)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___76_3880  ->
            match uu___76_3880 with
            | FStar_Syntax_Syntax.DECREASES uu____3881 -> false
            | uu____3884 -> true))
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
                   (fun uu___77_3902  ->
                      match uu___77_3902 with
                      | FStar_Syntax_Syntax.DECREASES uu____3903 -> false
                      | uu____3906 -> true)) in
            let rc1 =
              let uu___106_3908 = rc in
              let uu____3909 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___106_3908.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3909;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3916 -> lopt
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
    let uu____4006 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4006 in
  let arg_as_bounded_int uu____4034 =
    match uu____4034 with
    | (a,uu____4046) ->
        let uu____4053 =
          let uu____4054 = FStar_Syntax_Subst.compress a in
          uu____4054.FStar_Syntax_Syntax.n in
        (match uu____4053 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4064;
                FStar_Syntax_Syntax.vars = uu____4065;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4067;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4068;_},uu____4069)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4108 =
               let uu____4113 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4113) in
             FStar_Pervasives_Native.Some uu____4108
         | uu____4118 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4160 = f a in FStar_Pervasives_Native.Some uu____4160
    | uu____4161 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4211 = f a0 a1 in FStar_Pervasives_Native.Some uu____4211
    | uu____4212 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4261 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4261 in
  let binary_op as_a f res args =
    let uu____4317 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4317 in
  let as_primitive_step uu____4341 =
    match uu____4341 with
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
           let uu____4389 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4389) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4417 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4417) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4438 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4438) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4466 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4466) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4494 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4494) in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4611 =
          let uu____4620 = as_a a in
          let uu____4623 = as_b b in (uu____4620, uu____4623) in
        (match uu____4611 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4638 =
               let uu____4639 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4639 in
             FStar_Pervasives_Native.Some uu____4638
         | uu____4640 -> FStar_Pervasives_Native.None)
    | uu____4649 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4663 =
        let uu____4664 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4664 in
      mk uu____4663 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4674 =
      let uu____4677 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4677 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4674 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4709 =
      let uu____4710 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4710 in
    FStar_Syntax_Embeddings.embed_int rng uu____4709 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4728 = arg_as_string a1 in
        (match uu____4728 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4734 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4734 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4747 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4747
              | uu____4748 -> FStar_Pervasives_Native.None)
         | uu____4753 -> FStar_Pervasives_Native.None)
    | uu____4756 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4766 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4766 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4790 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4801 =
          let uu____4822 = arg_as_string fn in
          let uu____4825 = arg_as_int from_line in
          let uu____4828 = arg_as_int from_col in
          let uu____4831 = arg_as_int to_line in
          let uu____4834 = arg_as_int to_col in
          (uu____4822, uu____4825, uu____4828, uu____4831, uu____4834) in
        (match uu____4801 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4865 =
                 let uu____4866 = FStar_BigInt.to_int_fs from_l in
                 let uu____4867 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4866 uu____4867 in
               let uu____4868 =
                 let uu____4869 = FStar_BigInt.to_int_fs to_l in
                 let uu____4870 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4869 uu____4870 in
               FStar_Range.mk_range fn1 uu____4865 uu____4868 in
             let uu____4871 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4871
         | uu____4876 -> FStar_Pervasives_Native.None)
    | uu____4897 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4924)::(a1,uu____4926)::(a2,uu____4928)::[] ->
        let uu____4965 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4965 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4978 -> FStar_Pervasives_Native.None)
    | uu____4979 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5006)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5015 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5039 =
      let uu____5054 =
        let uu____5069 =
          let uu____5084 =
            let uu____5099 =
              let uu____5114 =
                let uu____5129 =
                  let uu____5144 =
                    let uu____5159 =
                      let uu____5174 =
                        let uu____5189 =
                          let uu____5204 =
                            let uu____5219 =
                              let uu____5234 =
                                let uu____5249 =
                                  let uu____5264 =
                                    let uu____5279 =
                                      let uu____5294 =
                                        let uu____5309 =
                                          let uu____5324 =
                                            let uu____5339 =
                                              let uu____5354 =
                                                let uu____5367 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5367,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string')) in
                                              let uu____5374 =
                                                let uu____5389 =
                                                  let uu____5402 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5402,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.unembed_char_safe)
                                                       string_of_list')) in
                                                let uu____5413 =
                                                  let uu____5428 =
                                                    let uu____5443 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5443,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5452 =
                                                    let uu____5469 =
                                                      let uu____5484 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5484,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5493 =
                                                      let uu____5510 =
                                                        let uu____5529 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5529,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5510] in
                                                    uu____5469 :: uu____5493 in
                                                  uu____5428 :: uu____5452 in
                                                uu____5389 :: uu____5413 in
                                              uu____5354 :: uu____5374 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5339 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5324 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____5309 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____5294 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____5279 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       FStar_Syntax_Embeddings.embed_string
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____5747 =
                                                FStar_BigInt.to_int_fs x in
                                              FStar_String.make uu____5747 y)))
                                    :: uu____5264 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5249 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5234 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5219 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5204 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5189 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5174 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5914 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5914)))
                      :: uu____5159 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5940 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5940)))
                    :: uu____5144 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5966 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5966)))
                  :: uu____5129 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5992 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5992)))
                :: uu____5114 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5099 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5084 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5069 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5054 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5039 in
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
      let uu____6142 =
        let uu____6143 =
          let uu____6144 = FStar_Syntax_Syntax.as_arg c in [uu____6144] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6143 in
      uu____6142 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6179 =
              let uu____6192 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6192, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6212  ->
                        fun uu____6213  ->
                          match (uu____6212, uu____6213) with
                          | ((int_to_t1,x),(uu____6232,y)) ->
                              let uu____6242 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6242))) in
            let uu____6243 =
              let uu____6258 =
                let uu____6271 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6271, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6291  ->
                          fun uu____6292  ->
                            match (uu____6291, uu____6292) with
                            | ((int_to_t1,x),(uu____6311,y)) ->
                                let uu____6321 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6321))) in
              let uu____6322 =
                let uu____6337 =
                  let uu____6350 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6350, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6370  ->
                            fun uu____6371  ->
                              match (uu____6370, uu____6371) with
                              | ((int_to_t1,x),(uu____6390,y)) ->
                                  let uu____6400 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6400))) in
                [uu____6337] in
              uu____6258 :: uu____6322 in
            uu____6179 :: uu____6243)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6490)::(a1,uu____6492)::(a2,uu____6494)::[] ->
        let uu____6531 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6531 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6537 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6537.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6537.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6541 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6541.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6541.FStar_Syntax_Syntax.vars)
                })
         | uu____6542 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6544)::uu____6545::(a1,uu____6547)::(a2,uu____6549)::[] ->
        let uu____6598 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6598 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6604 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6604.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6604.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6608 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6608.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6608.FStar_Syntax_Syntax.vars)
                })
         | uu____6609 -> FStar_Pervasives_Native.None)
    | uu____6610 -> failwith "Unexpected number of arguments" in
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
      let uu____6629 =
        let uu____6630 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6630 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6629
    with | uu____6636 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6640 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6640) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6700  ->
           fun subst1  ->
             match uu____6700 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6741,uu____6742)) ->
                      let uu____6801 = b in
                      (match uu____6801 with
                       | (bv,uu____6809) ->
                           let uu____6810 =
                             let uu____6811 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6811 in
                           if uu____6810
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6816 = unembed_binder term1 in
                              match uu____6816 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6823 =
                                      let uu___111_6824 = bv in
                                      let uu____6825 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_6824.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_6824.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6825
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6823 in
                                  let b_for_x =
                                    let uu____6829 =
                                      let uu____6836 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6836) in
                                    FStar_Syntax_Syntax.NT uu____6829 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_6845  ->
                                         match uu___78_6845 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6846,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6848;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6849;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6854 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6855 -> subst1)) env []
let reduce_primops:
  'Auu____6872 'Auu____6873 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6873) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6872 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6914 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6914
          then tm
          else
            (let uu____6916 = FStar_Syntax_Util.head_and_args tm in
             match uu____6916 with
             | (head1,args) ->
                 let uu____6953 =
                   let uu____6954 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6954.FStar_Syntax_Syntax.n in
                 (match uu____6953 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6958 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6958 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6975  ->
                                   let uu____6976 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6977 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6984 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6976 uu____6977 uu____6984);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6989  ->
                                   let uu____6990 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6990);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6993  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6995 =
                                 prim_step.interpretation psc args in
                               match uu____6995 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7001  ->
                                         let uu____7002 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7002);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7008  ->
                                         let uu____7009 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7010 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7009 uu____7010);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7011 ->
                           (log_primops cfg
                              (fun uu____7015  ->
                                 let uu____7016 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7016);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7020  ->
                            let uu____7021 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7021);
                       (match args with
                        | (a1,uu____7023)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7040 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7052  ->
                            let uu____7053 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7053);
                       (match args with
                        | (t,uu____7055)::(r,uu____7057)::[] ->
                            let uu____7084 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7084 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7088 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7088.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7088.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7091 -> tm))
                  | uu____7100 -> tm))
let reduce_equality:
  'Auu____7105 'Auu____7106 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7106) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7105 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___113_7144 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___113_7144.tcenv);
           delta_level = (uu___113_7144.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7144.strong);
           memoize_lazy = (uu___113_7144.memoize_lazy)
         }) tm
let maybe_simplify_aux:
  'Auu____7151 'Auu____7152 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7152) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7151 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7194 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7194
          then tm1
          else
            (let w t =
               let uu___114_7206 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7206.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7206.FStar_Syntax_Syntax.vars)
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
               | uu____7223 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7228 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7228
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7249 =
                 match uu____7249 with
                 | (t1,q) ->
                     let uu____7262 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7262 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7290 -> (t1, q)) in
               let uu____7299 = FStar_Syntax_Util.head_and_args t in
               match uu____7299 with
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
                         FStar_Syntax_Syntax.pos = uu____7396;
                         FStar_Syntax_Syntax.vars = uu____7397;_},uu____7398);
                    FStar_Syntax_Syntax.pos = uu____7399;
                    FStar_Syntax_Syntax.vars = uu____7400;_},args)
                 ->
                 let uu____7426 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7426
                 then
                   let uu____7427 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7427 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7482)::
                        (uu____7483,(arg,uu____7485))::[] ->
                        maybe_auto_squash arg
                    | (uu____7550,(arg,uu____7552))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7553)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7618)::uu____7619::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7682::(FStar_Pervasives_Native.Some (false
                                   ),uu____7683)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7746 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7762 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7762
                    then
                      let uu____7763 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7763 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7818)::uu____7819::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7882::(FStar_Pervasives_Native.Some (true
                                     ),uu____7883)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7946)::
                          (uu____7947,(arg,uu____7949))::[] ->
                          maybe_auto_squash arg
                      | (uu____8014,(arg,uu____8016))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8017)::[]
                          -> maybe_auto_squash arg
                      | uu____8082 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8098 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8098
                       then
                         let uu____8099 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8099 with
                         | uu____8154::(FStar_Pervasives_Native.Some (true
                                        ),uu____8155)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8218)::uu____8219::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8282)::
                             (uu____8283,(arg,uu____8285))::[] ->
                             maybe_auto_squash arg
                         | (uu____8350,(p,uu____8352))::(uu____8353,(q,uu____8355))::[]
                             ->
                             let uu____8420 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8420
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8422 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8438 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8438
                          then
                            let uu____8439 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8439 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8494)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8533)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8572 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8588 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8588
                             then
                               match args with
                               | (t,uu____8590)::[] ->
                                   let uu____8607 =
                                     let uu____8608 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8608.FStar_Syntax_Syntax.n in
                                   (match uu____8607 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8611::[],body,uu____8613) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8640 -> tm1)
                                    | uu____8643 -> tm1)
                               | (uu____8644,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8645))::
                                   (t,uu____8647)::[] ->
                                   let uu____8686 =
                                     let uu____8687 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8687.FStar_Syntax_Syntax.n in
                                   (match uu____8686 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8690::[],body,uu____8692) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8719 -> tm1)
                                    | uu____8722 -> tm1)
                               | uu____8723 -> tm1
                             else
                               (let uu____8733 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8733
                                then
                                  match args with
                                  | (t,uu____8735)::[] ->
                                      let uu____8752 =
                                        let uu____8753 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8753.FStar_Syntax_Syntax.n in
                                      (match uu____8752 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8756::[],body,uu____8758)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8785 -> tm1)
                                       | uu____8788 -> tm1)
                                  | (uu____8789,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8790))::(t,uu____8792)::[] ->
                                      let uu____8831 =
                                        let uu____8832 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8832.FStar_Syntax_Syntax.n in
                                      (match uu____8831 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8835::[],body,uu____8837)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8864 -> tm1)
                                       | uu____8867 -> tm1)
                                  | uu____8868 -> tm1
                                else
                                  (let uu____8878 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8878
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8879;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8880;_},uu____8881)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8898;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8899;_},uu____8900)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8917 -> tm1
                                   else
                                     (let uu____8927 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8927 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8947 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8957;
                    FStar_Syntax_Syntax.vars = uu____8958;_},args)
                 ->
                 let uu____8980 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8980
                 then
                   let uu____8981 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8981 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9036)::
                        (uu____9037,(arg,uu____9039))::[] ->
                        maybe_auto_squash arg
                    | (uu____9104,(arg,uu____9106))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9107)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9172)::uu____9173::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9236::(FStar_Pervasives_Native.Some (false
                                   ),uu____9237)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9300 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9316 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9316
                    then
                      let uu____9317 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9317 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9372)::uu____9373::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9436::(FStar_Pervasives_Native.Some (true
                                     ),uu____9437)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9500)::
                          (uu____9501,(arg,uu____9503))::[] ->
                          maybe_auto_squash arg
                      | (uu____9568,(arg,uu____9570))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9571)::[]
                          -> maybe_auto_squash arg
                      | uu____9636 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9652 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9652
                       then
                         let uu____9653 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9653 with
                         | uu____9708::(FStar_Pervasives_Native.Some (true
                                        ),uu____9709)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9772)::uu____9773::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9836)::
                             (uu____9837,(arg,uu____9839))::[] ->
                             maybe_auto_squash arg
                         | (uu____9904,(p,uu____9906))::(uu____9907,(q,uu____9909))::[]
                             ->
                             let uu____9974 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9974
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9976 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9992 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9992
                          then
                            let uu____9993 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9993 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10048)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10087)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10126 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10142 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10142
                             then
                               match args with
                               | (t,uu____10144)::[] ->
                                   let uu____10161 =
                                     let uu____10162 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10162.FStar_Syntax_Syntax.n in
                                   (match uu____10161 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10165::[],body,uu____10167) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10194 -> tm1)
                                    | uu____10197 -> tm1)
                               | (uu____10198,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10199))::
                                   (t,uu____10201)::[] ->
                                   let uu____10240 =
                                     let uu____10241 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10241.FStar_Syntax_Syntax.n in
                                   (match uu____10240 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10244::[],body,uu____10246) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10273 -> tm1)
                                    | uu____10276 -> tm1)
                               | uu____10277 -> tm1
                             else
                               (let uu____10287 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10287
                                then
                                  match args with
                                  | (t,uu____10289)::[] ->
                                      let uu____10306 =
                                        let uu____10307 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10307.FStar_Syntax_Syntax.n in
                                      (match uu____10306 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10310::[],body,uu____10312)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10339 -> tm1)
                                       | uu____10342 -> tm1)
                                  | (uu____10343,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10344))::(t,uu____10346)::[] ->
                                      let uu____10385 =
                                        let uu____10386 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10386.FStar_Syntax_Syntax.n in
                                      (match uu____10385 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10389::[],body,uu____10391)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10418 -> tm1)
                                       | uu____10421 -> tm1)
                                  | uu____10422 -> tm1
                                else
                                  (let uu____10432 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10432
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10433;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10434;_},uu____10435)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10452;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10453;_},uu____10454)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10471 -> tm1
                                   else
                                     (let uu____10481 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10481 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10501 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10510 -> tm1)
let maybe_simplify:
  'Auu____10517 'Auu____10518 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10518) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10517 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10561 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10561
           then
             let uu____10562 = FStar_Syntax_Print.term_to_string tm in
             let uu____10563 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10562 uu____10563
           else ());
          tm'
let is_norm_request:
  'Auu____10569 .
    FStar_Syntax_Syntax.term -> 'Auu____10569 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10582 =
        let uu____10589 =
          let uu____10590 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10590.FStar_Syntax_Syntax.n in
        (uu____10589, args) in
      match uu____10582 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10596::uu____10597::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10601::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10606::uu____10607::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10610 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___79_10621  ->
    match uu___79_10621 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10627 =
          let uu____10630 =
            let uu____10631 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10631 in
          [uu____10630] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10627
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10646 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10646) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10684 =
          let uu____10687 =
            let uu____10692 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10692 s in
          FStar_All.pipe_right uu____10687 FStar_Util.must in
        FStar_All.pipe_right uu____10684 tr_norm_steps in
      match args with
      | uu____10717::(tm,uu____10719)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10742)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10757)::uu____10758::(tm,uu____10760)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10800 =
              let uu____10803 = full_norm steps in parse_steps uu____10803 in
            Beta :: uu____10800 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10812 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___80_10829  ->
    match uu___80_10829 with
    | (App
        (uu____10832,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10833;
                       FStar_Syntax_Syntax.vars = uu____10834;_},uu____10835,uu____10836))::uu____10837
        -> true
    | uu____10844 -> false
let firstn:
  'Auu____10850 .
    Prims.int ->
      'Auu____10850 Prims.list ->
        ('Auu____10850 Prims.list,'Auu____10850 Prims.list)
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
          (uu____10886,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10887;
                         FStar_Syntax_Syntax.vars = uu____10888;_},uu____10889,uu____10890))::uu____10891
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10898 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11045  ->
               let uu____11046 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11047 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11048 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11055 =
                 let uu____11056 =
                   let uu____11059 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11059 in
                 stack_to_string uu____11056 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11046 uu____11047 uu____11048 uu____11055);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11082 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11107 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11124 =
                 let uu____11125 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11126 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11125 uu____11126 in
               failwith uu____11124
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11127 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11144 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11145 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11146;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11147;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11150;
                 FStar_Syntax_Syntax.fv_delta = uu____11151;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11152;
                 FStar_Syntax_Syntax.fv_delta = uu____11153;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11154);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11162 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11162 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11168  ->
                     let uu____11169 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11170 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11169 uu____11170);
                if b
                then
                  (let uu____11171 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11171 t1 fv)
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
                 let uu___115_11210 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11210.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11210.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11243 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11243) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11251 = cfg in
                 let uu____11252 =
                   FStar_List.filter
                     (fun uu___81_11255  ->
                        match uu___81_11255 with
                        | UnfoldOnly uu____11256 -> false
                        | NoDeltaSteps  -> false
                        | uu____11259 -> true) cfg.steps in
                 {
                   steps = uu____11252;
                   tcenv = (uu___116_11251.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11251.primitive_steps);
                   strong = (uu___116_11251.strong);
                   memoize_lazy = (uu___116_11251.memoize_lazy)
                 } in
               let uu____11260 = get_norm_request (norm cfg' env []) args in
               (match uu____11260 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11276 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11281  ->
                                match uu___82_11281 with
                                | UnfoldUntil uu____11282 -> true
                                | UnfoldOnly uu____11283 -> true
                                | uu____11286 -> false)) in
                      if uu____11276
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___117_11291 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___117_11291.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11291.primitive_steps);
                        strong = (uu___117_11291.strong);
                        memoize_lazy = (uu___117_11291.memoize_lazy)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11298 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11298
                      then
                        let uu____11301 =
                          let uu____11302 =
                            let uu____11307 = FStar_Util.now () in
                            (t1, uu____11307) in
                          Debug uu____11302 in
                        uu____11301 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11311 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11311
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11318 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11318
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11321 =
                      let uu____11328 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11328, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11321 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11341  ->
                         match uu___83_11341 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11344 =
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
                 if uu____11344
                 then false
                 else
                   (let uu____11346 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11353  ->
                              match uu___84_11353 with
                              | UnfoldOnly uu____11354 -> true
                              | uu____11357 -> false)) in
                    match uu____11346 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11361 -> should_delta) in
               (log cfg
                  (fun uu____11369  ->
                     let uu____11370 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11371 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11372 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11370 uu____11371 uu____11372);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11375 = lookup_bvar env x in
               (match uu____11375 with
                | Univ uu____11378 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11427 = FStar_ST.op_Bang r in
                      (match uu____11427 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11545  ->
                                 let uu____11546 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11547 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11546
                                   uu____11547);
                            (let uu____11548 =
                               let uu____11549 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11549.FStar_Syntax_Syntax.n in
                             match uu____11548 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11552 ->
                                 norm cfg env2 stack t'
                             | uu____11569 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11639)::uu____11640 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11649)::uu____11650 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11660,uu____11661))::stack_rest ->
                    (match c with
                     | Univ uu____11665 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11674 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11695  ->
                                    let uu____11696 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11696);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11736  ->
                                    let uu____11737 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11737);
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
                       (fun uu____11815  ->
                          let uu____11816 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11816);
                     norm cfg env stack1 t1)
                | (Debug uu____11817)::uu____11818 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11825 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11825
                    else
                      (let uu____11827 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11827 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11869  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11897 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11897
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11907 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11907)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_11912 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_11912.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_11912.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11913 -> lopt in
                           (log cfg
                              (fun uu____11919  ->
                                 let uu____11920 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11920);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_11929 = cfg in
                               {
                                 steps = (uu___119_11929.steps);
                                 tcenv = (uu___119_11929.tcenv);
                                 delta_level = (uu___119_11929.delta_level);
                                 primitive_steps =
                                   (uu___119_11929.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_11929.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11940)::uu____11941 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11948 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11948
                    else
                      (let uu____11950 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11950 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11992  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12020 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12020
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12030 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12030)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12035 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12035.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12035.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12036 -> lopt in
                           (log cfg
                              (fun uu____12042  ->
                                 let uu____12043 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12043);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12052 = cfg in
                               {
                                 steps = (uu___119_12052.steps);
                                 tcenv = (uu___119_12052.tcenv);
                                 delta_level = (uu___119_12052.delta_level);
                                 primitive_steps =
                                   (uu___119_12052.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12052.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12063)::uu____12064 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12075 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12075
                    else
                      (let uu____12077 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12077 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12119  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12147 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12147
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12157 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12157)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12162 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12162.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12162.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12163 -> lopt in
                           (log cfg
                              (fun uu____12169  ->
                                 let uu____12170 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12170);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12179 = cfg in
                               {
                                 steps = (uu___119_12179.steps);
                                 tcenv = (uu___119_12179.tcenv);
                                 delta_level = (uu___119_12179.delta_level);
                                 primitive_steps =
                                   (uu___119_12179.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12179.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12190)::uu____12191 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12202 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12202
                    else
                      (let uu____12204 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12204 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12246  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12274 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12274
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12284 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12284)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12289 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12289.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12289.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12290 -> lopt in
                           (log cfg
                              (fun uu____12296  ->
                                 let uu____12297 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12297);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12306 = cfg in
                               {
                                 steps = (uu___119_12306.steps);
                                 tcenv = (uu___119_12306.tcenv);
                                 delta_level = (uu___119_12306.delta_level);
                                 primitive_steps =
                                   (uu___119_12306.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12306.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12317)::uu____12318 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12333 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12333
                    else
                      (let uu____12335 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12335 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12377  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12405 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12405
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12415 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12415)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12420 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12420.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12420.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12421 -> lopt in
                           (log cfg
                              (fun uu____12427  ->
                                 let uu____12428 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12428);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12437 = cfg in
                               {
                                 steps = (uu___119_12437.steps);
                                 tcenv = (uu___119_12437.tcenv);
                                 delta_level = (uu___119_12437.delta_level);
                                 primitive_steps =
                                   (uu___119_12437.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12437.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12448 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12448
                    else
                      (let uu____12450 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12450 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12492  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12520 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12520
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12530 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12530)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12535 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12535.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12535.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12536 -> lopt in
                           (log cfg
                              (fun uu____12542  ->
                                 let uu____12543 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12543);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12552 = cfg in
                               {
                                 steps = (uu___119_12552.steps);
                                 tcenv = (uu___119_12552.tcenv);
                                 delta_level = (uu___119_12552.delta_level);
                                 primitive_steps =
                                   (uu___119_12552.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12552.memoize_lazy)
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
                      (fun uu____12601  ->
                         fun stack1  ->
                           match uu____12601 with
                           | (a,aq) ->
                               let uu____12613 =
                                 let uu____12614 =
                                   let uu____12621 =
                                     let uu____12622 =
                                       let uu____12653 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12653, false) in
                                     Clos uu____12622 in
                                   (uu____12621, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12614 in
                               uu____12613 :: stack1) args) in
               (log cfg
                  (fun uu____12737  ->
                     let uu____12738 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12738);
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
                             ((let uu___120_12774 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_12774.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_12774.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12775 ->
                      let uu____12780 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12780)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12783 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12783 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12814 =
                          let uu____12815 =
                            let uu____12822 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_12824 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_12824.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_12824.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12822) in
                          FStar_Syntax_Syntax.Tm_refine uu____12815 in
                        mk uu____12814 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12843 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12843
               else
                 (let uu____12845 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12845 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12853 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12877  -> dummy :: env1) env) in
                        norm_comp cfg uu____12853 c1 in
                      let t2 =
                        let uu____12899 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12899 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12958)::uu____12959 ->
                    (log cfg
                       (fun uu____12970  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12971)::uu____12972 ->
                    (log cfg
                       (fun uu____12983  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12984,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12985;
                                   FStar_Syntax_Syntax.vars = uu____12986;_},uu____12987,uu____12988))::uu____12989
                    ->
                    (log cfg
                       (fun uu____12998  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12999)::uu____13000 ->
                    (log cfg
                       (fun uu____13011  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13012 ->
                    (log cfg
                       (fun uu____13015  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13019  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13036 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13036
                         | FStar_Util.Inr c ->
                             let uu____13044 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13044 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13057 =
                               let uu____13058 =
                                 let uu____13085 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13085, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13058 in
                             mk uu____13057 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13104 ->
                           let uu____13105 =
                             let uu____13106 =
                               let uu____13107 =
                                 let uu____13134 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13134, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13107 in
                             mk uu____13106 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13105))))
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
                         let uu____13244 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13244 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13264 = cfg in
                               let uu____13265 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___122_13264.steps);
                                 tcenv = uu____13265;
                                 delta_level = (uu___122_13264.delta_level);
                                 primitive_steps =
                                   (uu___122_13264.primitive_steps);
                                 strong = (uu___122_13264.strong);
                                 memoize_lazy = (uu___122_13264.memoize_lazy)
                               } in
                             let norm1 t2 =
                               let uu____13270 =
                                 let uu____13271 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13271 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13270 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___123_13274 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13274.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13274.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13275 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13275
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13286,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13287;
                               FStar_Syntax_Syntax.lbunivs = uu____13288;
                               FStar_Syntax_Syntax.lbtyp = uu____13289;
                               FStar_Syntax_Syntax.lbeff = uu____13290;
                               FStar_Syntax_Syntax.lbdef = uu____13291;_}::uu____13292),uu____13293)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13329 =
                 (let uu____13332 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13332) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13334 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13334))) in
               if uu____13329
               then
                 let binder =
                   let uu____13336 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13336 in
                 let env1 =
                   let uu____13346 =
                     let uu____13353 =
                       let uu____13354 =
                         let uu____13385 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13385,
                           false) in
                       Clos uu____13354 in
                     ((FStar_Pervasives_Native.Some binder), uu____13353) in
                   uu____13346 :: env in
                 (log cfg
                    (fun uu____13478  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13480 =
                    let uu____13485 =
                      let uu____13486 =
                        let uu____13487 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13487
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13486] in
                    FStar_Syntax_Subst.open_term uu____13485 body in
                  match uu____13480 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13496  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13504 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13504 in
                          FStar_Util.Inl
                            (let uu___124_13514 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_13514.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_13514.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13517  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___125_13519 = lb in
                           let uu____13520 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_13519.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_13519.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13520
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13555  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___126_13578 = cfg in
                           {
                             steps = (uu___126_13578.steps);
                             tcenv = (uu___126_13578.tcenv);
                             delta_level = (uu___126_13578.delta_level);
                             primitive_steps =
                               (uu___126_13578.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___126_13578.memoize_lazy)
                           } in
                         log cfg1
                           (fun uu____13581  ->
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
               let uu____13598 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13598 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13634 =
                               let uu___127_13635 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13635.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13635.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13634 in
                           let uu____13636 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13636 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13662 =
                                   FStar_List.map (fun uu____13678  -> dummy)
                                     lbs1 in
                                 let uu____13679 =
                                   let uu____13688 =
                                     FStar_List.map
                                       (fun uu____13708  -> dummy) xs1 in
                                   FStar_List.append uu____13688 env in
                                 FStar_List.append uu____13662 uu____13679 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13732 =
                                       let uu___128_13733 = rc in
                                       let uu____13734 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_13733.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13734;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_13733.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13732
                                 | uu____13741 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___129_13745 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_13745.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_13745.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13755 =
                        FStar_List.map (fun uu____13771  -> dummy) lbs2 in
                      FStar_List.append uu____13755 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13779 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13779 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_13795 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_13795.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_13795.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13822 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13822
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13841 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13917  ->
                        match uu____13917 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14038 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14038.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14038.FStar_Syntax_Syntax.sort)
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
               (match uu____13841 with
                | (rec_env,memos,uu____14251) ->
                    let uu____14304 =
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
                             let uu____14615 =
                               let uu____14622 =
                                 let uu____14623 =
                                   let uu____14654 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14654, false) in
                                 Clos uu____14623 in
                               (FStar_Pervasives_Native.None, uu____14622) in
                             uu____14615 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14764  ->
                     let uu____14765 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14765);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14787 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14789::uu____14790 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14795) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14796 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14827 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14841 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14841
                              | uu____14852 -> m in
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
              let uu____14864 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14864 in
            let uu____14865 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14865 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14878  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14889  ->
                      let uu____14890 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14891 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14890
                        uu____14891);
                 (let t1 =
                    let uu____14893 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____14895 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____14895) in
                    if uu____14893
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
                    | (UnivArgs (us',uu____14905))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____14960 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____14963 ->
                        let uu____14966 =
                          let uu____14967 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14967 in
                        failwith uu____14966
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
                let uu____14988 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____14988
                then
                  let uu___132_14989 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_14989.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_14989.primitive_steps);
                    strong = (uu___132_14989.strong);
                    memoize_lazy = (uu___132_14989.memoize_lazy)
                  }
                else
                  (let uu___133_14991 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_14991.tcenv);
                     delta_level = (uu___133_14991.delta_level);
                     primitive_steps = (uu___133_14991.primitive_steps);
                     strong = (uu___133_14991.strong);
                     memoize_lazy = (uu___133_14991.memoize_lazy)
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
                  (fun uu____15020  ->
                     let uu____15021 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15022 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15021
                       uu____15022);
                (let uu____15023 =
                   let uu____15024 = FStar_Syntax_Subst.compress head2 in
                   uu____15024.FStar_Syntax_Syntax.n in
                 match uu____15023 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15042 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15042 with
                      | (uu____15043,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15049 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15057 =
                                   let uu____15058 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15058.FStar_Syntax_Syntax.n in
                                 match uu____15057 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15064,uu____15065))
                                     ->
                                     let uu____15074 =
                                       let uu____15075 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15075.FStar_Syntax_Syntax.n in
                                     (match uu____15074 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15081,msrc,uu____15083))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15092 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15092
                                      | uu____15093 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15094 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15095 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15095 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15100 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15100.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15100.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15100.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15101 = FStar_List.tl stack in
                                    let uu____15102 =
                                      let uu____15103 =
                                        let uu____15106 =
                                          let uu____15107 =
                                            let uu____15120 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15120) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15107 in
                                        FStar_Syntax_Syntax.mk uu____15106 in
                                      uu____15103
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15101 uu____15102
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15136 =
                                      let uu____15137 = is_return body in
                                      match uu____15137 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15141;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15142;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15147 -> false in
                                    if uu____15136
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
                                         let uu____15170 =
                                           let uu____15173 =
                                             let uu____15174 =
                                               let uu____15191 =
                                                 let uu____15194 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15194] in
                                               (uu____15191, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15174 in
                                           FStar_Syntax_Syntax.mk uu____15173 in
                                         uu____15170
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15210 =
                                           let uu____15211 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15211.FStar_Syntax_Syntax.n in
                                         match uu____15210 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15217::uu____15218::[])
                                             ->
                                             let uu____15225 =
                                               let uu____15228 =
                                                 let uu____15229 =
                                                   let uu____15236 =
                                                     let uu____15239 =
                                                       let uu____15240 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15240 in
                                                     let uu____15241 =
                                                       let uu____15244 =
                                                         let uu____15245 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15245 in
                                                       [uu____15244] in
                                                     uu____15239 ::
                                                       uu____15241 in
                                                   (bind1, uu____15236) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15229 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15228 in
                                             uu____15225
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15253 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15259 =
                                           let uu____15262 =
                                             let uu____15263 =
                                               let uu____15278 =
                                                 let uu____15281 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15282 =
                                                   let uu____15285 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15286 =
                                                     let uu____15289 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15290 =
                                                       let uu____15293 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15294 =
                                                         let uu____15297 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15298 =
                                                           let uu____15301 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15301] in
                                                         uu____15297 ::
                                                           uu____15298 in
                                                       uu____15293 ::
                                                         uu____15294 in
                                                     uu____15289 ::
                                                       uu____15290 in
                                                   uu____15285 :: uu____15286 in
                                                 uu____15281 :: uu____15282 in
                                               (bind_inst, uu____15278) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15263 in
                                           FStar_Syntax_Syntax.mk uu____15262 in
                                         uu____15259
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15312  ->
                                            let uu____15313 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15313);
                                       (let uu____15314 = FStar_List.tl stack in
                                        norm cfg env uu____15314 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15338 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15338 with
                      | (uu____15339,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15374 =
                                  let uu____15375 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15375.FStar_Syntax_Syntax.n in
                                match uu____15374 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15381) -> t2
                                | uu____15386 -> head3 in
                              let uu____15387 =
                                let uu____15388 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15388.FStar_Syntax_Syntax.n in
                              match uu____15387 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15394 -> FStar_Pervasives_Native.None in
                            let uu____15395 = maybe_extract_fv head3 in
                            match uu____15395 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15405 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15405
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15410 = maybe_extract_fv head4 in
                                  match uu____15410 with
                                  | FStar_Pervasives_Native.Some uu____15415
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15416 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15421 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15436 =
                              match uu____15436 with
                              | (e,q) ->
                                  let uu____15443 =
                                    let uu____15444 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15444.FStar_Syntax_Syntax.n in
                                  (match uu____15443 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15459 -> false) in
                            let uu____15460 =
                              let uu____15461 =
                                let uu____15468 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15468 :: args in
                              FStar_Util.for_some is_arg_impure uu____15461 in
                            if uu____15460
                            then
                              let uu____15473 =
                                let uu____15474 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15474 in
                              failwith uu____15473
                            else ());
                           (let uu____15476 = maybe_unfold_action head_app in
                            match uu____15476 with
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
                                let uu____15513 = FStar_List.tl stack in
                                norm cfg env uu____15513 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15515) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15539 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15539 in
                     (log cfg
                        (fun uu____15543  ->
                           let uu____15544 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15544);
                      (let uu____15545 = FStar_List.tl stack in
                       norm cfg env uu____15545 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15547) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15672  ->
                               match uu____15672 with
                               | (pat,wopt,tm) ->
                                   let uu____15720 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15720))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____15752 = FStar_List.tl stack in
                     norm cfg env uu____15752 tm
                 | uu____15753 -> fallback ())
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
              (fun uu____15767  ->
                 let uu____15768 = FStar_Ident.string_of_lid msrc in
                 let uu____15769 = FStar_Ident.string_of_lid mtgt in
                 let uu____15770 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15768
                   uu____15769 uu____15770);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____15772 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15772 with
               | (uu____15773,return_repr) ->
                   let return_inst =
                     let uu____15782 =
                       let uu____15783 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15783.FStar_Syntax_Syntax.n in
                     match uu____15782 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15789::[]) ->
                         let uu____15796 =
                           let uu____15799 =
                             let uu____15800 =
                               let uu____15807 =
                                 let uu____15810 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15810] in
                               (return_tm, uu____15807) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15800 in
                           FStar_Syntax_Syntax.mk uu____15799 in
                         uu____15796 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15818 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15821 =
                     let uu____15824 =
                       let uu____15825 =
                         let uu____15840 =
                           let uu____15843 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15844 =
                             let uu____15847 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15847] in
                           uu____15843 :: uu____15844 in
                         (return_inst, uu____15840) in
                       FStar_Syntax_Syntax.Tm_app uu____15825 in
                     FStar_Syntax_Syntax.mk uu____15824 in
                   uu____15821 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15856 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15856 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15859 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15859
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15860;
                     FStar_TypeChecker_Env.mtarget = uu____15861;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15862;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15877;
                     FStar_TypeChecker_Env.mtarget = uu____15878;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15879;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15903 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____15904 = FStar_Syntax_Util.mk_reify e in
                   lift uu____15903 t FStar_Syntax_Syntax.tun uu____15904)
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
                (fun uu____15960  ->
                   match uu____15960 with
                   | (a,imp) ->
                       let uu____15971 = norm cfg env [] a in
                       (uu____15971, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_15985 = comp in
            let uu____15986 =
              let uu____15987 =
                let uu____15996 = norm cfg env [] t in
                let uu____15997 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15996, uu____15997) in
              FStar_Syntax_Syntax.Total uu____15987 in
            {
              FStar_Syntax_Syntax.n = uu____15986;
              FStar_Syntax_Syntax.pos =
                (uu___135_15985.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_15985.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_16012 = comp in
            let uu____16013 =
              let uu____16014 =
                let uu____16023 = norm cfg env [] t in
                let uu____16024 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16023, uu____16024) in
              FStar_Syntax_Syntax.GTotal uu____16014 in
            {
              FStar_Syntax_Syntax.n = uu____16013;
              FStar_Syntax_Syntax.pos =
                (uu___136_16012.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16012.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16076  ->
                      match uu____16076 with
                      | (a,i) ->
                          let uu____16087 = norm cfg env [] a in
                          (uu____16087, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16098  ->
                      match uu___85_16098 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16102 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16102
                      | f -> f)) in
            let uu___137_16106 = comp in
            let uu____16107 =
              let uu____16108 =
                let uu___138_16109 = ct in
                let uu____16110 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16111 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16114 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16110;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16109.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16111;
                  FStar_Syntax_Syntax.effect_args = uu____16114;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16108 in
            {
              FStar_Syntax_Syntax.n = uu____16107;
              FStar_Syntax_Syntax.pos =
                (uu___137_16106.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16106.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16125  ->
        match uu____16125 with
        | (x,imp) ->
            let uu____16128 =
              let uu___139_16129 = x in
              let uu____16130 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16129.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16129.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16130
              } in
            (uu____16128, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16136 =
          FStar_List.fold_left
            (fun uu____16154  ->
               fun b  ->
                 match uu____16154 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16136 with | (nbs,uu____16194) -> FStar_List.rev nbs
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
            let uu____16210 =
              let uu___140_16211 = rc in
              let uu____16212 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16211.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16212;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16211.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16210
        | uu____16219 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16232  ->
               let uu____16233 = FStar_Syntax_Print.tag_of_term t in
               let uu____16234 = FStar_Syntax_Print.term_to_string t in
               let uu____16235 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16242 =
                 let uu____16243 =
                   let uu____16246 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16246 in
                 stack_to_string uu____16243 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16233 uu____16234 uu____16235 uu____16242);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16275 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16275
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16277 =
                     let uu____16278 =
                       let uu____16279 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16279 in
                     FStar_Util.string_of_int uu____16278 in
                   let uu____16284 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16285 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16277 uu____16284 uu____16285
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16339  ->
                     let uu____16340 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16340);
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
               let uu____16376 =
                 let uu___141_16377 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16377.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16377.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16376
           | (Arg (Univ uu____16378,uu____16379,uu____16380))::uu____16381 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16384,uu____16385))::uu____16386 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16402),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16455  ->
                     let uu____16456 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16456);
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
                  (let uu____16466 = FStar_ST.op_Bang m in
                   match uu____16466 with
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
                   | FStar_Pervasives_Native.Some (uu____16603,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16650 =
                 log cfg
                   (fun uu____16654  ->
                      let uu____16655 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16655);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16659 =
                 let uu____16660 = FStar_Syntax_Subst.compress t in
                 uu____16660.FStar_Syntax_Syntax.n in
               (match uu____16659 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16687 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16687 in
                    (log cfg
                       (fun uu____16691  ->
                          let uu____16692 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16692);
                     (let uu____16693 = FStar_List.tl stack in
                      norm cfg env1 uu____16693 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16694);
                       FStar_Syntax_Syntax.pos = uu____16695;
                       FStar_Syntax_Syntax.vars = uu____16696;_},(e,uu____16698)::[])
                    -> norm cfg env1 stack' e
                | uu____16727 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16738 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16738
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16750  ->
                     let uu____16751 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16751);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16756 =
                   log cfg
                     (fun uu____16761  ->
                        let uu____16762 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16763 =
                          let uu____16764 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16781  ->
                                    match uu____16781 with
                                    | (p,uu____16791,uu____16792) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16764
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16762 uu____16763);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_16809  ->
                                match uu___86_16809 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16810 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___142_16814 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_16814.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_16814.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_16814.memoize_lazy)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16846 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16867 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16927  ->
                                    fun uu____16928  ->
                                      match (uu____16927, uu____16928) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17019 = norm_pat env3 p1 in
                                          (match uu____17019 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16867 with
                           | (pats1,env3) ->
                               ((let uu___143_17101 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17101.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17120 = x in
                            let uu____17121 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17120.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17120.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17121
                            } in
                          ((let uu___145_17135 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17135.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17146 = x in
                            let uu____17147 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17146.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17146.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17147
                            } in
                          ((let uu___147_17161 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17161.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___148_17177 = x in
                            let uu____17178 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17177.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17177.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17178
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___149_17185 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17185.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17195 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17209 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17209 with
                                  | (p,wopt,e) ->
                                      let uu____17229 = norm_pat env1 p in
                                      (match uu____17229 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17254 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17254 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17260 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17260) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17270) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17275 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17276;
                         FStar_Syntax_Syntax.fv_delta = uu____17277;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17278;
                         FStar_Syntax_Syntax.fv_delta = uu____17279;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17280);_}
                       -> true
                   | uu____17287 -> false in
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
                   let uu____17432 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17432 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17519 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17558 ->
                                 let uu____17559 =
                                   let uu____17560 = is_cons head1 in
                                   Prims.op_Negation uu____17560 in
                                 FStar_Util.Inr uu____17559)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17585 =
                              let uu____17586 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17586.FStar_Syntax_Syntax.n in
                            (match uu____17585 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17604 ->
                                 let uu____17605 =
                                   let uu____17606 = is_cons head1 in
                                   Prims.op_Negation uu____17606 in
                                 FStar_Util.Inr uu____17605))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17675)::rest_a,(p1,uu____17678)::rest_p) ->
                       let uu____17722 = matches_pat t1 p1 in
                       (match uu____17722 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17771 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17877 = matches_pat scrutinee1 p1 in
                       (match uu____17877 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17917  ->
                                  let uu____17918 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17919 =
                                    let uu____17920 =
                                      FStar_List.map
                                        (fun uu____17930  ->
                                           match uu____17930 with
                                           | (uu____17935,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17920
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17918 uu____17919);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____17966  ->
                                       match uu____17966 with
                                       | (bv,t1) ->
                                           let uu____17989 =
                                             let uu____17996 =
                                               let uu____17999 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____17999 in
                                             let uu____18000 =
                                               let uu____18001 =
                                                 let uu____18032 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18032, false) in
                                               Clos uu____18001 in
                                             (uu____17996, uu____18000) in
                                           uu____17989 :: env2) env1 s in
                              let uu____18149 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18149))) in
                 let uu____18150 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18150
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18171  ->
                match uu___87_18171 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18175 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18181 -> d in
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
            let uu___150_18206 = config s e in
            {
              steps = (uu___150_18206.steps);
              tcenv = (uu___150_18206.tcenv);
              delta_level = (uu___150_18206.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18206.strong);
              memoize_lazy = (uu___150_18206.memoize_lazy)
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
      fun t  -> let uu____18231 = config s e in norm_comp uu____18231 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18244 = config [] env in norm_universe uu____18244 [] u
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
        let uu____18262 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18262 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18269 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18288 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18288.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18288.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18295 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18295
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
                  let uu___152_18304 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18304.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18304.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18304.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___153_18306 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18306.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18306.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18306.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18306.FStar_Syntax_Syntax.flags)
                  } in
            let uu___154_18307 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18307.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18307.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18309 -> c
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
        let uu____18321 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18321 in
      let uu____18328 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18328
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18332  ->
                 let uu____18333 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18333)
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
            ((let uu____18350 =
                let uu____18355 =
                  let uu____18356 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18356 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18355) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18350);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18367 = config [AllowUnboundUniverses] env in
          norm_comp uu____18367 [] c
        with
        | e ->
            ((let uu____18380 =
                let uu____18385 =
                  let uu____18386 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18386 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18385) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18380);
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
                   let uu____18423 =
                     let uu____18424 =
                       let uu____18431 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18431) in
                     FStar_Syntax_Syntax.Tm_refine uu____18424 in
                   mk uu____18423 t01.FStar_Syntax_Syntax.pos
               | uu____18436 -> t2)
          | uu____18437 -> t2 in
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
        let uu____18477 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18477 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18506 ->
                 let uu____18513 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18513 with
                  | (actuals,uu____18523,uu____18524) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18538 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18538 with
                         | (binders,args) ->
                             let uu____18555 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18555
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
      | uu____18563 ->
          let uu____18564 = FStar_Syntax_Util.head_and_args t in
          (match uu____18564 with
           | (head1,args) ->
               let uu____18601 =
                 let uu____18602 = FStar_Syntax_Subst.compress head1 in
                 uu____18602.FStar_Syntax_Syntax.n in
               (match uu____18601 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18605,thead) ->
                    let uu____18631 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18631 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18673 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18681 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18681.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18681.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18681.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18681.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18681.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18681.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18681.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18681.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18681.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18681.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18681.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18681.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18681.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18681.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18681.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18681.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18681.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18681.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18681.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18681.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18681.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18681.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18681.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18681.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18681.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18681.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18681.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18681.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18681.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18681.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18681.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18673 with
                            | (uu____18682,ty,uu____18684) ->
                                eta_expand_with_type env t ty))
                | uu____18685 ->
                    let uu____18686 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18694 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18694.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18694.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18694.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18694.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18694.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18694.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18694.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18694.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18694.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18694.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18694.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18694.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18694.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18694.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18694.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18694.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18694.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18694.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18694.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18694.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18694.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18694.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18694.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18694.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18694.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18694.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18694.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18694.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18694.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18694.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18694.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18686 with
                     | (uu____18695,ty,uu____18697) ->
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
            | (uu____18771,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18777,FStar_Util.Inl t) ->
                let uu____18783 =
                  let uu____18786 =
                    let uu____18787 =
                      let uu____18800 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18800) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18787 in
                  FStar_Syntax_Syntax.mk uu____18786 in
                uu____18783 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18804 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18804 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18831 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18886 ->
                    let uu____18887 =
                      let uu____18896 =
                        let uu____18897 = FStar_Syntax_Subst.compress t3 in
                        uu____18897.FStar_Syntax_Syntax.n in
                      (uu____18896, tc) in
                    (match uu____18887 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18922) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18959) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____18998,FStar_Util.Inl uu____18999) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19022 -> failwith "Impossible") in
              (match uu____18831 with
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
          let uu____19127 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19127 with
          | (univ_names1,binders1,tc) ->
              let uu____19185 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19185)
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
          let uu____19220 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19220 with
          | (univ_names1,binders1,tc) ->
              let uu____19280 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19280)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19313 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19313 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19341 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19341.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19341.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19341.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19341.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19362 = s in
          let uu____19363 =
            let uu____19364 =
              let uu____19373 = FStar_List.map (elim_uvars env) sigs in
              (uu____19373, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19364 in
          {
            FStar_Syntax_Syntax.sigel = uu____19363;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19362.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19362.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19362.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19362.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19390 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19390 with
           | (univ_names1,uu____19408,typ1) ->
               let uu___163_19422 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19422.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19422.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19422.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19422.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19428 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19428 with
           | (univ_names1,uu____19446,typ1) ->
               let uu___164_19460 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19460.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19460.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19460.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19460.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19494 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19494 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19517 =
                            let uu____19518 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19518 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19517 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___165_19521 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19521.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19521.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___166_19522 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19522.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19522.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19522.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19522.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19534 = s in
          let uu____19535 =
            let uu____19536 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19536 in
          {
            FStar_Syntax_Syntax.sigel = uu____19535;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19534.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19534.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19534.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19534.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19540 = elim_uvars_aux_t env us [] t in
          (match uu____19540 with
           | (us1,uu____19558,t1) ->
               let uu___168_19572 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19572.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19572.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19572.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19572.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19573 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19575 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19575 with
           | (univs1,binders,signature) ->
               let uu____19603 =
                 let uu____19612 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19612 with
                 | (univs_opening,univs2) ->
                     let uu____19639 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19639) in
               (match uu____19603 with
                | (univs_opening,univs_closing) ->
                    let uu____19656 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19662 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19663 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19662, uu____19663) in
                    (match uu____19656 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19685 =
                           match uu____19685 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19703 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19703 with
                                | (us1,t1) ->
                                    let uu____19714 =
                                      let uu____19719 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19726 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19719, uu____19726) in
                                    (match uu____19714 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19739 =
                                           let uu____19744 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19753 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19744, uu____19753) in
                                         (match uu____19739 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19769 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19769 in
                                              let uu____19770 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19770 with
                                               | (uu____19791,uu____19792,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19807 =
                                                       let uu____19808 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19808 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19807 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19813 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19813 with
                           | (uu____19826,uu____19827,t1) -> t1 in
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
                             | uu____19887 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19904 =
                               let uu____19905 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19905.FStar_Syntax_Syntax.n in
                             match uu____19904 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19964 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____19993 =
                               let uu____19994 =
                                 FStar_Syntax_Subst.compress t in
                               uu____19994.FStar_Syntax_Syntax.n in
                             match uu____19993 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20015) ->
                                 let uu____20036 = destruct_action_body body in
                                 (match uu____20036 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20081 ->
                                 let uu____20082 = destruct_action_body t in
                                 (match uu____20082 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20131 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20131 with
                           | (action_univs,t) ->
                               let uu____20140 = destruct_action_typ_templ t in
                               (match uu____20140 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20181 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20181.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20181.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___170_20183 = ed in
                           let uu____20184 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20185 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20186 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20187 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20188 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20189 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20190 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20191 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20192 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20193 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20194 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20195 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20196 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20197 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20183.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20183.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20184;
                             FStar_Syntax_Syntax.bind_wp = uu____20185;
                             FStar_Syntax_Syntax.if_then_else = uu____20186;
                             FStar_Syntax_Syntax.ite_wp = uu____20187;
                             FStar_Syntax_Syntax.stronger = uu____20188;
                             FStar_Syntax_Syntax.close_wp = uu____20189;
                             FStar_Syntax_Syntax.assert_p = uu____20190;
                             FStar_Syntax_Syntax.assume_p = uu____20191;
                             FStar_Syntax_Syntax.null_wp = uu____20192;
                             FStar_Syntax_Syntax.trivial = uu____20193;
                             FStar_Syntax_Syntax.repr = uu____20194;
                             FStar_Syntax_Syntax.return_repr = uu____20195;
                             FStar_Syntax_Syntax.bind_repr = uu____20196;
                             FStar_Syntax_Syntax.actions = uu____20197
                           } in
                         let uu___171_20200 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20200.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20200.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20200.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20200.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20217 =
            match uu___88_20217 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20244 = elim_uvars_aux_t env us [] t in
                (match uu____20244 with
                 | (us1,uu____20268,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___172_20287 = sub_eff in
            let uu____20288 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20291 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20287.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20287.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20288;
              FStar_Syntax_Syntax.lift = uu____20291
            } in
          let uu___173_20294 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20294.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20294.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20294.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20294.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20304 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20304 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20338 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20338.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20338.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20338.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20338.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20349 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t