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
                                              let uu____5352 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5352,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5359 =
                                              let uu____5374 =
                                                let uu____5387 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5387,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5398 =
                                                let uu____5413 =
                                                  let uu____5428 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5428,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5437 =
                                                  let uu____5454 =
                                                    let uu____5469 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5469,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5478 =
                                                    let uu____5495 =
                                                      let uu____5514 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5514,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5495] in
                                                  uu____5454 :: uu____5478 in
                                                uu____5413 :: uu____5437 in
                                              uu____5374 :: uu____5398 in
                                            uu____5339 :: uu____5359 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5324 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5309 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5294 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5279 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5264 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5732 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5732 y)))
                                  :: uu____5249 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5234 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5219 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5204 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
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
                                let uu____5878 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5878)))
                      :: uu____5159 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5904 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5904)))
                    :: uu____5144 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5930 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5930)))
                  :: uu____5129 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5956 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5956)))
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
      let uu____6106 =
        let uu____6107 =
          let uu____6108 = FStar_Syntax_Syntax.as_arg c in [uu____6108] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6107 in
      uu____6106 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6143 =
              let uu____6156 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6156, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6176  ->
                        fun uu____6177  ->
                          match (uu____6176, uu____6177) with
                          | ((int_to_t1,x),(uu____6196,y)) ->
                              let uu____6206 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6206))) in
            let uu____6207 =
              let uu____6222 =
                let uu____6235 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6235, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6255  ->
                          fun uu____6256  ->
                            match (uu____6255, uu____6256) with
                            | ((int_to_t1,x),(uu____6275,y)) ->
                                let uu____6285 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6285))) in
              let uu____6286 =
                let uu____6301 =
                  let uu____6314 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6314, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6334  ->
                            fun uu____6335  ->
                              match (uu____6334, uu____6335) with
                              | ((int_to_t1,x),(uu____6354,y)) ->
                                  let uu____6364 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6364))) in
                [uu____6301] in
              uu____6222 :: uu____6286 in
            uu____6143 :: uu____6207)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6454)::(a1,uu____6456)::(a2,uu____6458)::[] ->
        let uu____6495 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6495 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6501 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6501.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6501.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6505 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6505.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6505.FStar_Syntax_Syntax.vars)
                })
         | uu____6506 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6508)::uu____6509::(a1,uu____6511)::(a2,uu____6513)::[] ->
        let uu____6562 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6562 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6568 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6568.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6568.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6572 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6572.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6572.FStar_Syntax_Syntax.vars)
                })
         | uu____6573 -> FStar_Pervasives_Native.None)
    | uu____6574 -> failwith "Unexpected number of arguments" in
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
      let uu____6593 =
        let uu____6594 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6594 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6593
    with | uu____6600 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6604 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6604) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6664  ->
           fun subst1  ->
             match uu____6664 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6705,uu____6706)) ->
                      let uu____6765 = b in
                      (match uu____6765 with
                       | (bv,uu____6773) ->
                           let uu____6774 =
                             let uu____6775 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6775 in
                           if uu____6774
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6780 = unembed_binder term1 in
                              match uu____6780 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6787 =
                                      let uu___111_6788 = bv in
                                      let uu____6789 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_6788.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_6788.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6789
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6787 in
                                  let b_for_x =
                                    let uu____6793 =
                                      let uu____6800 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6800) in
                                    FStar_Syntax_Syntax.NT uu____6793 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_6809  ->
                                         match uu___78_6809 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6810,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6812;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6813;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6818 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6819 -> subst1)) env []
let reduce_primops:
  'Auu____6836 'Auu____6837 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6837) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6836 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6878 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6878
          then tm
          else
            (let uu____6880 = FStar_Syntax_Util.head_and_args tm in
             match uu____6880 with
             | (head1,args) ->
                 let uu____6917 =
                   let uu____6918 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6918.FStar_Syntax_Syntax.n in
                 (match uu____6917 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6922 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6922 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6939  ->
                                   let uu____6940 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6941 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6948 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6940 uu____6941 uu____6948);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6953  ->
                                   let uu____6954 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6954);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6957  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6959 =
                                 prim_step.interpretation psc args in
                               match uu____6959 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6965  ->
                                         let uu____6966 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6966);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6972  ->
                                         let uu____6973 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6974 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6973 uu____6974);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6975 ->
                           (log_primops cfg
                              (fun uu____6979  ->
                                 let uu____6980 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6980);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6984  ->
                            let uu____6985 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6985);
                       (match args with
                        | (a1,uu____6987)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7004 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7016  ->
                            let uu____7017 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7017);
                       (match args with
                        | (t,uu____7019)::(r,uu____7021)::[] ->
                            let uu____7048 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7048 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7052 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7052.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7052.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7055 -> tm))
                  | uu____7064 -> tm))
let reduce_equality:
  'Auu____7069 'Auu____7070 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7070) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7069 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___113_7108 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___113_7108.tcenv);
           delta_level = (uu___113_7108.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7108.strong);
           memoize_lazy = (uu___113_7108.memoize_lazy)
         }) tm
let maybe_simplify_aux:
  'Auu____7115 'Auu____7116 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7116) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7115 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7158 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7158
          then tm1
          else
            (let w t =
               let uu___114_7170 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7170.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7170.FStar_Syntax_Syntax.vars)
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
               | uu____7187 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7192 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7192
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7213 =
                 match uu____7213 with
                 | (t1,q) ->
                     let uu____7226 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7226 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7254 -> (t1, q)) in
               let uu____7263 = FStar_Syntax_Util.head_and_args t in
               match uu____7263 with
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
                         FStar_Syntax_Syntax.pos = uu____7360;
                         FStar_Syntax_Syntax.vars = uu____7361;_},uu____7362);
                    FStar_Syntax_Syntax.pos = uu____7363;
                    FStar_Syntax_Syntax.vars = uu____7364;_},args)
                 ->
                 let uu____7390 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7390
                 then
                   let uu____7391 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7391 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7446)::
                        (uu____7447,(arg,uu____7449))::[] ->
                        maybe_auto_squash arg
                    | (uu____7514,(arg,uu____7516))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7517)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7582)::uu____7583::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7646::(FStar_Pervasives_Native.Some (false
                                   ),uu____7647)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7710 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7726 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7726
                    then
                      let uu____7727 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7727 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7782)::uu____7783::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7846::(FStar_Pervasives_Native.Some (true
                                     ),uu____7847)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7910)::
                          (uu____7911,(arg,uu____7913))::[] ->
                          maybe_auto_squash arg
                      | (uu____7978,(arg,uu____7980))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7981)::[]
                          -> maybe_auto_squash arg
                      | uu____8046 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8062 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8062
                       then
                         let uu____8063 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8063 with
                         | uu____8118::(FStar_Pervasives_Native.Some (true
                                        ),uu____8119)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8182)::uu____8183::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8246)::
                             (uu____8247,(arg,uu____8249))::[] ->
                             maybe_auto_squash arg
                         | (uu____8314,(p,uu____8316))::(uu____8317,(q,uu____8319))::[]
                             ->
                             let uu____8384 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8384
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8386 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8402 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8402
                          then
                            let uu____8403 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8403 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8458)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8497)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8536 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8552 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8552
                             then
                               match args with
                               | (t,uu____8554)::[] ->
                                   let uu____8571 =
                                     let uu____8572 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8572.FStar_Syntax_Syntax.n in
                                   (match uu____8571 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8575::[],body,uu____8577) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8604 -> tm1)
                                    | uu____8607 -> tm1)
                               | (uu____8608,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8609))::
                                   (t,uu____8611)::[] ->
                                   let uu____8650 =
                                     let uu____8651 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8651.FStar_Syntax_Syntax.n in
                                   (match uu____8650 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8654::[],body,uu____8656) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8683 -> tm1)
                                    | uu____8686 -> tm1)
                               | uu____8687 -> tm1
                             else
                               (let uu____8697 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8697
                                then
                                  match args with
                                  | (t,uu____8699)::[] ->
                                      let uu____8716 =
                                        let uu____8717 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8717.FStar_Syntax_Syntax.n in
                                      (match uu____8716 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8720::[],body,uu____8722)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8749 -> tm1)
                                       | uu____8752 -> tm1)
                                  | (uu____8753,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8754))::(t,uu____8756)::[] ->
                                      let uu____8795 =
                                        let uu____8796 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8796.FStar_Syntax_Syntax.n in
                                      (match uu____8795 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8799::[],body,uu____8801)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8828 -> tm1)
                                       | uu____8831 -> tm1)
                                  | uu____8832 -> tm1
                                else
                                  (let uu____8842 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8842
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8843;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8844;_},uu____8845)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8862;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8863;_},uu____8864)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8881 -> tm1
                                   else
                                     (let uu____8891 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8891 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8911 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8921;
                    FStar_Syntax_Syntax.vars = uu____8922;_},args)
                 ->
                 let uu____8944 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8944
                 then
                   let uu____8945 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8945 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9000)::
                        (uu____9001,(arg,uu____9003))::[] ->
                        maybe_auto_squash arg
                    | (uu____9068,(arg,uu____9070))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9071)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9136)::uu____9137::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9200::(FStar_Pervasives_Native.Some (false
                                   ),uu____9201)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9264 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9280 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9280
                    then
                      let uu____9281 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9281 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9336)::uu____9337::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9400::(FStar_Pervasives_Native.Some (true
                                     ),uu____9401)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9464)::
                          (uu____9465,(arg,uu____9467))::[] ->
                          maybe_auto_squash arg
                      | (uu____9532,(arg,uu____9534))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9535)::[]
                          -> maybe_auto_squash arg
                      | uu____9600 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9616 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9616
                       then
                         let uu____9617 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9617 with
                         | uu____9672::(FStar_Pervasives_Native.Some (true
                                        ),uu____9673)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9736)::uu____9737::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9800)::
                             (uu____9801,(arg,uu____9803))::[] ->
                             maybe_auto_squash arg
                         | (uu____9868,(p,uu____9870))::(uu____9871,(q,uu____9873))::[]
                             ->
                             let uu____9938 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9938
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9940 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9956 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9956
                          then
                            let uu____9957 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9957 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10012)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10051)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10090 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10106 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10106
                             then
                               match args with
                               | (t,uu____10108)::[] ->
                                   let uu____10125 =
                                     let uu____10126 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10126.FStar_Syntax_Syntax.n in
                                   (match uu____10125 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10129::[],body,uu____10131) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10158 -> tm1)
                                    | uu____10161 -> tm1)
                               | (uu____10162,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10163))::
                                   (t,uu____10165)::[] ->
                                   let uu____10204 =
                                     let uu____10205 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10205.FStar_Syntax_Syntax.n in
                                   (match uu____10204 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10208::[],body,uu____10210) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10237 -> tm1)
                                    | uu____10240 -> tm1)
                               | uu____10241 -> tm1
                             else
                               (let uu____10251 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10251
                                then
                                  match args with
                                  | (t,uu____10253)::[] ->
                                      let uu____10270 =
                                        let uu____10271 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10271.FStar_Syntax_Syntax.n in
                                      (match uu____10270 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10274::[],body,uu____10276)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10303 -> tm1)
                                       | uu____10306 -> tm1)
                                  | (uu____10307,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10308))::(t,uu____10310)::[] ->
                                      let uu____10349 =
                                        let uu____10350 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10350.FStar_Syntax_Syntax.n in
                                      (match uu____10349 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10353::[],body,uu____10355)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10382 -> tm1)
                                       | uu____10385 -> tm1)
                                  | uu____10386 -> tm1
                                else
                                  (let uu____10396 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10396
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10397;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10398;_},uu____10399)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10416;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10417;_},uu____10418)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10435 -> tm1
                                   else
                                     (let uu____10445 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10445 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10465 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10474 -> tm1)
let maybe_simplify:
  'Auu____10481 'Auu____10482 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10482) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10481 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10525 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10525
           then
             let uu____10526 = FStar_Syntax_Print.term_to_string tm in
             let uu____10527 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10526 uu____10527
           else ());
          tm'
let is_norm_request:
  'Auu____10533 .
    FStar_Syntax_Syntax.term -> 'Auu____10533 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10546 =
        let uu____10553 =
          let uu____10554 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10554.FStar_Syntax_Syntax.n in
        (uu____10553, args) in
      match uu____10546 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10560::uu____10561::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10565::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10570::uu____10571::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10574 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___79_10585  ->
    match uu___79_10585 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10591 =
          let uu____10594 =
            let uu____10595 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10595 in
          [uu____10594] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10591
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10610 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10610) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10648 =
          let uu____10651 =
            let uu____10656 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10656 s in
          FStar_All.pipe_right uu____10651 FStar_Util.must in
        FStar_All.pipe_right uu____10648 tr_norm_steps in
      match args with
      | uu____10681::(tm,uu____10683)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10706)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10721)::uu____10722::(tm,uu____10724)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10764 =
              let uu____10767 = full_norm steps in parse_steps uu____10767 in
            Beta :: uu____10764 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10776 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___80_10793  ->
    match uu___80_10793 with
    | (App
        (uu____10796,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10797;
                       FStar_Syntax_Syntax.vars = uu____10798;_},uu____10799,uu____10800))::uu____10801
        -> true
    | uu____10808 -> false
let firstn:
  'Auu____10814 .
    Prims.int ->
      'Auu____10814 Prims.list ->
        ('Auu____10814 Prims.list,'Auu____10814 Prims.list)
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
          (uu____10850,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10851;
                         FStar_Syntax_Syntax.vars = uu____10852;_},uu____10853,uu____10854))::uu____10855
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10862 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11009  ->
               let uu____11010 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11011 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11012 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11019 =
                 let uu____11020 =
                   let uu____11023 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11023 in
                 stack_to_string uu____11020 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11010 uu____11011 uu____11012 uu____11019);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11046 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11071 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11088 =
                 let uu____11089 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11090 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11089 uu____11090 in
               failwith uu____11088
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11091 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11108 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11109 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11110;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11111;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11114;
                 FStar_Syntax_Syntax.fv_delta = uu____11115;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11116;
                 FStar_Syntax_Syntax.fv_delta = uu____11117;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11118);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11126 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11126 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11132  ->
                     let uu____11133 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11134 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11133 uu____11134);
                if b
                then
                  (let uu____11135 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11135 t1 fv)
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
                 let uu___115_11174 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11174.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11174.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11207 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11207) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11215 = cfg in
                 let uu____11216 =
                   FStar_List.filter
                     (fun uu___81_11219  ->
                        match uu___81_11219 with
                        | UnfoldOnly uu____11220 -> false
                        | NoDeltaSteps  -> false
                        | uu____11223 -> true) cfg.steps in
                 {
                   steps = uu____11216;
                   tcenv = (uu___116_11215.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11215.primitive_steps);
                   strong = (uu___116_11215.strong);
                   memoize_lazy = (uu___116_11215.memoize_lazy)
                 } in
               let uu____11224 = get_norm_request (norm cfg' env []) args in
               (match uu____11224 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11240 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11245  ->
                                match uu___82_11245 with
                                | UnfoldUntil uu____11246 -> true
                                | UnfoldOnly uu____11247 -> true
                                | uu____11250 -> false)) in
                      if uu____11240
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___117_11255 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___117_11255.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11255.primitive_steps);
                        strong = (uu___117_11255.strong);
                        memoize_lazy = (uu___117_11255.memoize_lazy)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11262 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11262
                      then
                        let uu____11265 =
                          let uu____11266 =
                            let uu____11271 = FStar_Util.now () in
                            (t1, uu____11271) in
                          Debug uu____11266 in
                        uu____11265 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11275 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11275
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11282 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11282
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11285 =
                      let uu____11292 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11292, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11285 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11305  ->
                         match uu___83_11305 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11308 =
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
                 if uu____11308
                 then false
                 else
                   (let uu____11310 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11317  ->
                              match uu___84_11317 with
                              | UnfoldOnly uu____11318 -> true
                              | uu____11321 -> false)) in
                    match uu____11310 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11325 -> should_delta) in
               (log cfg
                  (fun uu____11333  ->
                     let uu____11334 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11335 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11336 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11334 uu____11335 uu____11336);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11339 = lookup_bvar env x in
               (match uu____11339 with
                | Univ uu____11342 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11391 = FStar_ST.op_Bang r in
                      (match uu____11391 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11509  ->
                                 let uu____11510 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11511 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11510
                                   uu____11511);
                            (let uu____11512 =
                               let uu____11513 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11513.FStar_Syntax_Syntax.n in
                             match uu____11512 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11516 ->
                                 norm cfg env2 stack t'
                             | uu____11533 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11603)::uu____11604 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11613)::uu____11614 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11624,uu____11625))::stack_rest ->
                    (match c with
                     | Univ uu____11629 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11638 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11659  ->
                                    let uu____11660 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11660);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11700  ->
                                    let uu____11701 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11701);
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
                       (fun uu____11779  ->
                          let uu____11780 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11780);
                     norm cfg env stack1 t1)
                | (Debug uu____11781)::uu____11782 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11789 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11789
                    else
                      (let uu____11791 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11791 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11833  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11861 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11861
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11871 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11871)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_11876 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_11876.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_11876.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11877 -> lopt in
                           (log cfg
                              (fun uu____11883  ->
                                 let uu____11884 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11884);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_11893 = cfg in
                               {
                                 steps = (uu___119_11893.steps);
                                 tcenv = (uu___119_11893.tcenv);
                                 delta_level = (uu___119_11893.delta_level);
                                 primitive_steps =
                                   (uu___119_11893.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_11893.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11904)::uu____11905 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11912 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11912
                    else
                      (let uu____11914 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11914 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11956  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11984 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11984
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11994 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11994)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_11999 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_11999.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_11999.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12000 -> lopt in
                           (log cfg
                              (fun uu____12006  ->
                                 let uu____12007 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12007);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12016 = cfg in
                               {
                                 steps = (uu___119_12016.steps);
                                 tcenv = (uu___119_12016.tcenv);
                                 delta_level = (uu___119_12016.delta_level);
                                 primitive_steps =
                                   (uu___119_12016.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12016.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12027)::uu____12028 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12039 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12039
                    else
                      (let uu____12041 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12041 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12083  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12111 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12111
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12121 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12121)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12126 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12126.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12126.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12127 -> lopt in
                           (log cfg
                              (fun uu____12133  ->
                                 let uu____12134 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12134);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12143 = cfg in
                               {
                                 steps = (uu___119_12143.steps);
                                 tcenv = (uu___119_12143.tcenv);
                                 delta_level = (uu___119_12143.delta_level);
                                 primitive_steps =
                                   (uu___119_12143.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12143.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12154)::uu____12155 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12166 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12166
                    else
                      (let uu____12168 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12168 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12210  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12238 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12238
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12248 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12248)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12253 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12253.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12253.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12254 -> lopt in
                           (log cfg
                              (fun uu____12260  ->
                                 let uu____12261 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12261);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12270 = cfg in
                               {
                                 steps = (uu___119_12270.steps);
                                 tcenv = (uu___119_12270.tcenv);
                                 delta_level = (uu___119_12270.delta_level);
                                 primitive_steps =
                                   (uu___119_12270.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12270.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12281)::uu____12282 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12297 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12297
                    else
                      (let uu____12299 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12299 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12341  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12369 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12369
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12379 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12379)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12384 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12384.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12384.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12385 -> lopt in
                           (log cfg
                              (fun uu____12391  ->
                                 let uu____12392 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12392);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12401 = cfg in
                               {
                                 steps = (uu___119_12401.steps);
                                 tcenv = (uu___119_12401.tcenv);
                                 delta_level = (uu___119_12401.delta_level);
                                 primitive_steps =
                                   (uu___119_12401.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12401.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12412 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12412
                    else
                      (let uu____12414 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12414 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12456  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12484 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12484
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12494 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12494)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12499 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12499.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12499.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12500 -> lopt in
                           (log cfg
                              (fun uu____12506  ->
                                 let uu____12507 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12507);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12516 = cfg in
                               {
                                 steps = (uu___119_12516.steps);
                                 tcenv = (uu___119_12516.tcenv);
                                 delta_level = (uu___119_12516.delta_level);
                                 primitive_steps =
                                   (uu___119_12516.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12516.memoize_lazy)
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
                      (fun uu____12565  ->
                         fun stack1  ->
                           match uu____12565 with
                           | (a,aq) ->
                               let uu____12577 =
                                 let uu____12578 =
                                   let uu____12585 =
                                     let uu____12586 =
                                       let uu____12617 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12617, false) in
                                     Clos uu____12586 in
                                   (uu____12585, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12578 in
                               uu____12577 :: stack1) args) in
               (log cfg
                  (fun uu____12701  ->
                     let uu____12702 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12702);
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
                             ((let uu___120_12738 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_12738.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_12738.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12739 ->
                      let uu____12744 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12744)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12747 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12747 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12778 =
                          let uu____12779 =
                            let uu____12786 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_12788 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_12788.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_12788.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12786) in
                          FStar_Syntax_Syntax.Tm_refine uu____12779 in
                        mk uu____12778 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12807 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12807
               else
                 (let uu____12809 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12809 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12817 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12841  -> dummy :: env1) env) in
                        norm_comp cfg uu____12817 c1 in
                      let t2 =
                        let uu____12863 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12863 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12922)::uu____12923 ->
                    (log cfg
                       (fun uu____12934  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12935)::uu____12936 ->
                    (log cfg
                       (fun uu____12947  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12948,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12949;
                                   FStar_Syntax_Syntax.vars = uu____12950;_},uu____12951,uu____12952))::uu____12953
                    ->
                    (log cfg
                       (fun uu____12962  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12963)::uu____12964 ->
                    (log cfg
                       (fun uu____12975  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12976 ->
                    (log cfg
                       (fun uu____12979  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12983  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13000 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13000
                         | FStar_Util.Inr c ->
                             let uu____13008 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13008 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13021 =
                               let uu____13022 =
                                 let uu____13049 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13049, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13022 in
                             mk uu____13021 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13068 ->
                           let uu____13069 =
                             let uu____13070 =
                               let uu____13071 =
                                 let uu____13098 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13098, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13071 in
                             mk uu____13070 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13069))))
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
                         let uu____13208 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13208 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13228 = cfg in
                               let uu____13229 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___122_13228.steps);
                                 tcenv = uu____13229;
                                 delta_level = (uu___122_13228.delta_level);
                                 primitive_steps =
                                   (uu___122_13228.primitive_steps);
                                 strong = (uu___122_13228.strong);
                                 memoize_lazy = (uu___122_13228.memoize_lazy)
                               } in
                             let norm1 t2 =
                               let uu____13234 =
                                 let uu____13235 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13235 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13234 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___123_13238 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13238.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13238.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13239 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13239
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13250,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13251;
                               FStar_Syntax_Syntax.lbunivs = uu____13252;
                               FStar_Syntax_Syntax.lbtyp = uu____13253;
                               FStar_Syntax_Syntax.lbeff = uu____13254;
                               FStar_Syntax_Syntax.lbdef = uu____13255;_}::uu____13256),uu____13257)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13293 =
                 (let uu____13296 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13296) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13298 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13298))) in
               if uu____13293
               then
                 let binder =
                   let uu____13300 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13300 in
                 let env1 =
                   let uu____13310 =
                     let uu____13317 =
                       let uu____13318 =
                         let uu____13349 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13349,
                           false) in
                       Clos uu____13318 in
                     ((FStar_Pervasives_Native.Some binder), uu____13317) in
                   uu____13310 :: env in
                 (log cfg
                    (fun uu____13442  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13444 =
                    let uu____13449 =
                      let uu____13450 =
                        let uu____13451 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13451
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13450] in
                    FStar_Syntax_Subst.open_term uu____13449 body in
                  match uu____13444 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13460  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13468 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13468 in
                          FStar_Util.Inl
                            (let uu___124_13478 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_13478.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_13478.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13481  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___125_13483 = lb in
                           let uu____13484 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_13483.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_13483.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13484
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13519  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___126_13542 = cfg in
                           {
                             steps = (uu___126_13542.steps);
                             tcenv = (uu___126_13542.tcenv);
                             delta_level = (uu___126_13542.delta_level);
                             primitive_steps =
                               (uu___126_13542.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___126_13542.memoize_lazy)
                           } in
                         log cfg1
                           (fun uu____13545  ->
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
               let uu____13562 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13562 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13598 =
                               let uu___127_13599 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13599.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13599.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13598 in
                           let uu____13600 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13600 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13626 =
                                   FStar_List.map (fun uu____13642  -> dummy)
                                     lbs1 in
                                 let uu____13643 =
                                   let uu____13652 =
                                     FStar_List.map
                                       (fun uu____13672  -> dummy) xs1 in
                                   FStar_List.append uu____13652 env in
                                 FStar_List.append uu____13626 uu____13643 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13696 =
                                       let uu___128_13697 = rc in
                                       let uu____13698 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_13697.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13698;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_13697.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13696
                                 | uu____13705 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___129_13709 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_13709.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_13709.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13719 =
                        FStar_List.map (fun uu____13735  -> dummy) lbs2 in
                      FStar_List.append uu____13719 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13743 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13743 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_13759 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_13759.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_13759.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13786 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13786
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13805 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13881  ->
                        match uu____13881 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14002 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14002.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14002.FStar_Syntax_Syntax.sort)
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
               (match uu____13805 with
                | (rec_env,memos,uu____14215) ->
                    let uu____14268 =
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
                             let uu____14579 =
                               let uu____14586 =
                                 let uu____14587 =
                                   let uu____14618 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14618, false) in
                                 Clos uu____14587 in
                               (FStar_Pervasives_Native.None, uu____14586) in
                             uu____14579 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14728  ->
                     let uu____14729 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14729);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14751 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14753::uu____14754 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14759) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14760 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14791 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14805 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14805
                              | uu____14816 -> m in
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
              let uu____14828 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14828 in
            let uu____14829 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14829 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14842  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14853  ->
                      let uu____14854 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14855 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14854
                        uu____14855);
                 (let t1 =
                    let uu____14857 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____14859 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____14859) in
                    if uu____14857
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
                    | (UnivArgs (us',uu____14869))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____14924 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____14927 ->
                        let uu____14930 =
                          let uu____14931 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14931 in
                        failwith uu____14930
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
                let uu____14952 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____14952
                then
                  let uu___132_14953 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_14953.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_14953.primitive_steps);
                    strong = (uu___132_14953.strong);
                    memoize_lazy = (uu___132_14953.memoize_lazy)
                  }
                else
                  (let uu___133_14955 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_14955.tcenv);
                     delta_level = (uu___133_14955.delta_level);
                     primitive_steps = (uu___133_14955.primitive_steps);
                     strong = (uu___133_14955.strong);
                     memoize_lazy = (uu___133_14955.memoize_lazy)
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
                  (fun uu____14984  ->
                     let uu____14985 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____14986 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14985
                       uu____14986);
                (let uu____14987 =
                   let uu____14988 = FStar_Syntax_Subst.compress head2 in
                   uu____14988.FStar_Syntax_Syntax.n in
                 match uu____14987 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15006 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15006 with
                      | (uu____15007,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15013 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15021 =
                                   let uu____15022 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15022.FStar_Syntax_Syntax.n in
                                 match uu____15021 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15028,uu____15029))
                                     ->
                                     let uu____15038 =
                                       let uu____15039 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15039.FStar_Syntax_Syntax.n in
                                     (match uu____15038 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15045,msrc,uu____15047))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15056 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15056
                                      | uu____15057 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15058 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15059 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15059 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15064 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15064.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15064.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15064.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15065 = FStar_List.tl stack in
                                    let uu____15066 =
                                      let uu____15067 =
                                        let uu____15070 =
                                          let uu____15071 =
                                            let uu____15084 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15084) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15071 in
                                        FStar_Syntax_Syntax.mk uu____15070 in
                                      uu____15067
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15065 uu____15066
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15100 =
                                      let uu____15101 = is_return body in
                                      match uu____15101 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15105;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15106;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15111 -> false in
                                    if uu____15100
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
                                         let uu____15134 =
                                           let uu____15137 =
                                             let uu____15138 =
                                               let uu____15155 =
                                                 let uu____15158 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15158] in
                                               (uu____15155, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15138 in
                                           FStar_Syntax_Syntax.mk uu____15137 in
                                         uu____15134
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15174 =
                                           let uu____15175 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15175.FStar_Syntax_Syntax.n in
                                         match uu____15174 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15181::uu____15182::[])
                                             ->
                                             let uu____15189 =
                                               let uu____15192 =
                                                 let uu____15193 =
                                                   let uu____15200 =
                                                     let uu____15203 =
                                                       let uu____15204 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15204 in
                                                     let uu____15205 =
                                                       let uu____15208 =
                                                         let uu____15209 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15209 in
                                                       [uu____15208] in
                                                     uu____15203 ::
                                                       uu____15205 in
                                                   (bind1, uu____15200) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15193 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15192 in
                                             uu____15189
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15217 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15223 =
                                           let uu____15226 =
                                             let uu____15227 =
                                               let uu____15242 =
                                                 let uu____15245 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15246 =
                                                   let uu____15249 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15250 =
                                                     let uu____15253 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15254 =
                                                       let uu____15257 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15258 =
                                                         let uu____15261 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15262 =
                                                           let uu____15265 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15265] in
                                                         uu____15261 ::
                                                           uu____15262 in
                                                       uu____15257 ::
                                                         uu____15258 in
                                                     uu____15253 ::
                                                       uu____15254 in
                                                   uu____15249 :: uu____15250 in
                                                 uu____15245 :: uu____15246 in
                                               (bind_inst, uu____15242) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15227 in
                                           FStar_Syntax_Syntax.mk uu____15226 in
                                         uu____15223
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15276  ->
                                            let uu____15277 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15277);
                                       (let uu____15278 = FStar_List.tl stack in
                                        norm cfg env uu____15278 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15302 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15302 with
                      | (uu____15303,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15338 =
                                  let uu____15339 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15339.FStar_Syntax_Syntax.n in
                                match uu____15338 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15345) -> t2
                                | uu____15350 -> head3 in
                              let uu____15351 =
                                let uu____15352 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15352.FStar_Syntax_Syntax.n in
                              match uu____15351 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15358 -> FStar_Pervasives_Native.None in
                            let uu____15359 = maybe_extract_fv head3 in
                            match uu____15359 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15369 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15369
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15374 = maybe_extract_fv head4 in
                                  match uu____15374 with
                                  | FStar_Pervasives_Native.Some uu____15379
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15380 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15385 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15400 =
                              match uu____15400 with
                              | (e,q) ->
                                  let uu____15407 =
                                    let uu____15408 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15408.FStar_Syntax_Syntax.n in
                                  (match uu____15407 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15423 -> false) in
                            let uu____15424 =
                              let uu____15425 =
                                let uu____15432 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15432 :: args in
                              FStar_Util.for_some is_arg_impure uu____15425 in
                            if uu____15424
                            then
                              let uu____15437 =
                                let uu____15438 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15438 in
                              failwith uu____15437
                            else ());
                           (let uu____15440 = maybe_unfold_action head_app in
                            match uu____15440 with
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
                                let uu____15477 = FStar_List.tl stack in
                                norm cfg env uu____15477 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15479) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15503 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15503 in
                     (log cfg
                        (fun uu____15507  ->
                           let uu____15508 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15508);
                      (let uu____15509 = FStar_List.tl stack in
                       norm cfg env uu____15509 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15511) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15636  ->
                               match uu____15636 with
                               | (pat,wopt,tm) ->
                                   let uu____15684 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15684))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____15716 = FStar_List.tl stack in
                     norm cfg env uu____15716 tm
                 | uu____15717 -> fallback ())
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
              (fun uu____15731  ->
                 let uu____15732 = FStar_Ident.string_of_lid msrc in
                 let uu____15733 = FStar_Ident.string_of_lid mtgt in
                 let uu____15734 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15732
                   uu____15733 uu____15734);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____15736 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15736 with
               | (uu____15737,return_repr) ->
                   let return_inst =
                     let uu____15746 =
                       let uu____15747 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15747.FStar_Syntax_Syntax.n in
                     match uu____15746 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15753::[]) ->
                         let uu____15760 =
                           let uu____15763 =
                             let uu____15764 =
                               let uu____15771 =
                                 let uu____15774 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15774] in
                               (return_tm, uu____15771) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15764 in
                           FStar_Syntax_Syntax.mk uu____15763 in
                         uu____15760 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15782 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15785 =
                     let uu____15788 =
                       let uu____15789 =
                         let uu____15804 =
                           let uu____15807 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15808 =
                             let uu____15811 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15811] in
                           uu____15807 :: uu____15808 in
                         (return_inst, uu____15804) in
                       FStar_Syntax_Syntax.Tm_app uu____15789 in
                     FStar_Syntax_Syntax.mk uu____15788 in
                   uu____15785 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15820 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15820 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15823 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15823
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15824;
                     FStar_TypeChecker_Env.mtarget = uu____15825;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15826;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15841;
                     FStar_TypeChecker_Env.mtarget = uu____15842;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15843;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15867 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____15868 = FStar_Syntax_Util.mk_reify e in
                   lift uu____15867 t FStar_Syntax_Syntax.tun uu____15868)
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
                (fun uu____15924  ->
                   match uu____15924 with
                   | (a,imp) ->
                       let uu____15935 = norm cfg env [] a in
                       (uu____15935, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_15949 = comp in
            let uu____15950 =
              let uu____15951 =
                let uu____15960 = norm cfg env [] t in
                let uu____15961 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15960, uu____15961) in
              FStar_Syntax_Syntax.Total uu____15951 in
            {
              FStar_Syntax_Syntax.n = uu____15950;
              FStar_Syntax_Syntax.pos =
                (uu___135_15949.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_15949.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_15976 = comp in
            let uu____15977 =
              let uu____15978 =
                let uu____15987 = norm cfg env [] t in
                let uu____15988 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15987, uu____15988) in
              FStar_Syntax_Syntax.GTotal uu____15978 in
            {
              FStar_Syntax_Syntax.n = uu____15977;
              FStar_Syntax_Syntax.pos =
                (uu___136_15976.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_15976.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16040  ->
                      match uu____16040 with
                      | (a,i) ->
                          let uu____16051 = norm cfg env [] a in
                          (uu____16051, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16062  ->
                      match uu___85_16062 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16066 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16066
                      | f -> f)) in
            let uu___137_16070 = comp in
            let uu____16071 =
              let uu____16072 =
                let uu___138_16073 = ct in
                let uu____16074 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16075 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16078 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16074;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16073.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16075;
                  FStar_Syntax_Syntax.effect_args = uu____16078;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16072 in
            {
              FStar_Syntax_Syntax.n = uu____16071;
              FStar_Syntax_Syntax.pos =
                (uu___137_16070.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16070.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16089  ->
        match uu____16089 with
        | (x,imp) ->
            let uu____16092 =
              let uu___139_16093 = x in
              let uu____16094 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16093.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16093.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16094
              } in
            (uu____16092, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16100 =
          FStar_List.fold_left
            (fun uu____16118  ->
               fun b  ->
                 match uu____16118 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16100 with | (nbs,uu____16158) -> FStar_List.rev nbs
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
            let uu____16174 =
              let uu___140_16175 = rc in
              let uu____16176 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16175.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16176;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16175.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16174
        | uu____16183 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16196  ->
               let uu____16197 = FStar_Syntax_Print.tag_of_term t in
               let uu____16198 = FStar_Syntax_Print.term_to_string t in
               let uu____16199 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16206 =
                 let uu____16207 =
                   let uu____16210 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16210 in
                 stack_to_string uu____16207 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16197 uu____16198 uu____16199 uu____16206);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16239 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16239
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16241 =
                     let uu____16242 =
                       let uu____16243 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16243 in
                     FStar_Util.string_of_int uu____16242 in
                   let uu____16248 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16249 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16241 uu____16248 uu____16249
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16303  ->
                     let uu____16304 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16304);
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
               let uu____16340 =
                 let uu___141_16341 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16341.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16341.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16340
           | (Arg (Univ uu____16342,uu____16343,uu____16344))::uu____16345 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16348,uu____16349))::uu____16350 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16366),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16419  ->
                     let uu____16420 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16420);
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
                  (let uu____16430 = FStar_ST.op_Bang m in
                   match uu____16430 with
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
                   | FStar_Pervasives_Native.Some (uu____16567,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16614 =
                 log cfg
                   (fun uu____16618  ->
                      let uu____16619 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16619);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16623 =
                 let uu____16624 = FStar_Syntax_Subst.compress t in
                 uu____16624.FStar_Syntax_Syntax.n in
               (match uu____16623 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16651 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16651 in
                    (log cfg
                       (fun uu____16655  ->
                          let uu____16656 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16656);
                     (let uu____16657 = FStar_List.tl stack in
                      norm cfg env1 uu____16657 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16658);
                       FStar_Syntax_Syntax.pos = uu____16659;
                       FStar_Syntax_Syntax.vars = uu____16660;_},(e,uu____16662)::[])
                    -> norm cfg env1 stack' e
                | uu____16691 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16702 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16702
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16714  ->
                     let uu____16715 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16715);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16720 =
                   log cfg
                     (fun uu____16725  ->
                        let uu____16726 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16727 =
                          let uu____16728 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16745  ->
                                    match uu____16745 with
                                    | (p,uu____16755,uu____16756) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16728
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16726 uu____16727);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_16773  ->
                                match uu___86_16773 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16774 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___142_16778 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_16778.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_16778.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_16778.memoize_lazy)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16810 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16831 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16891  ->
                                    fun uu____16892  ->
                                      match (uu____16891, uu____16892) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____16983 = norm_pat env3 p1 in
                                          (match uu____16983 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16831 with
                           | (pats1,env3) ->
                               ((let uu___143_17065 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17065.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17084 = x in
                            let uu____17085 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17084.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17084.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17085
                            } in
                          ((let uu___145_17099 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17099.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17110 = x in
                            let uu____17111 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17110.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17110.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17111
                            } in
                          ((let uu___147_17125 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17125.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___148_17141 = x in
                            let uu____17142 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17141.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17141.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17142
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___149_17149 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17149.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17159 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17173 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17173 with
                                  | (p,wopt,e) ->
                                      let uu____17193 = norm_pat env1 p in
                                      (match uu____17193 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17218 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17218 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17224 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17224) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17234) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17239 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17240;
                         FStar_Syntax_Syntax.fv_delta = uu____17241;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17242;
                         FStar_Syntax_Syntax.fv_delta = uu____17243;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17244);_}
                       -> true
                   | uu____17251 -> false in
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
                   let uu____17396 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17396 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17483 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17522 ->
                                 let uu____17523 =
                                   let uu____17524 = is_cons head1 in
                                   Prims.op_Negation uu____17524 in
                                 FStar_Util.Inr uu____17523)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17549 =
                              let uu____17550 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17550.FStar_Syntax_Syntax.n in
                            (match uu____17549 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17568 ->
                                 let uu____17569 =
                                   let uu____17570 = is_cons head1 in
                                   Prims.op_Negation uu____17570 in
                                 FStar_Util.Inr uu____17569))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17639)::rest_a,(p1,uu____17642)::rest_p) ->
                       let uu____17686 = matches_pat t1 p1 in
                       (match uu____17686 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17735 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17841 = matches_pat scrutinee1 p1 in
                       (match uu____17841 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17881  ->
                                  let uu____17882 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17883 =
                                    let uu____17884 =
                                      FStar_List.map
                                        (fun uu____17894  ->
                                           match uu____17894 with
                                           | (uu____17899,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17884
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17882 uu____17883);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____17930  ->
                                       match uu____17930 with
                                       | (bv,t1) ->
                                           let uu____17953 =
                                             let uu____17960 =
                                               let uu____17963 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____17963 in
                                             let uu____17964 =
                                               let uu____17965 =
                                                 let uu____17996 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____17996, false) in
                                               Clos uu____17965 in
                                             (uu____17960, uu____17964) in
                                           uu____17953 :: env2) env1 s in
                              let uu____18113 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18113))) in
                 let uu____18114 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18114
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18135  ->
                match uu___87_18135 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18139 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18145 -> d in
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
            let uu___150_18170 = config s e in
            {
              steps = (uu___150_18170.steps);
              tcenv = (uu___150_18170.tcenv);
              delta_level = (uu___150_18170.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18170.strong);
              memoize_lazy = (uu___150_18170.memoize_lazy)
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
      fun t  -> let uu____18195 = config s e in norm_comp uu____18195 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18208 = config [] env in norm_universe uu____18208 [] u
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
        let uu____18226 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18226 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18233 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18252 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18252.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18252.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18259 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18259
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
                  let uu___152_18268 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18268.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18268.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18268.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___153_18270 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18270.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18270.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18270.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18270.FStar_Syntax_Syntax.flags)
                  } in
            let uu___154_18271 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18271.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18271.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18273 -> c
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
        let uu____18285 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18285 in
      let uu____18292 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18292
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18296  ->
                 let uu____18297 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18297)
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
            ((let uu____18314 =
                let uu____18319 =
                  let uu____18320 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18320 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18319) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18314);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18331 = config [AllowUnboundUniverses] env in
          norm_comp uu____18331 [] c
        with
        | e ->
            ((let uu____18344 =
                let uu____18349 =
                  let uu____18350 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18350 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18349) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18344);
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
                   let uu____18387 =
                     let uu____18388 =
                       let uu____18395 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18395) in
                     FStar_Syntax_Syntax.Tm_refine uu____18388 in
                   mk uu____18387 t01.FStar_Syntax_Syntax.pos
               | uu____18400 -> t2)
          | uu____18401 -> t2 in
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
        let uu____18441 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18441 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18470 ->
                 let uu____18477 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18477 with
                  | (actuals,uu____18487,uu____18488) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18502 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18502 with
                         | (binders,args) ->
                             let uu____18519 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18519
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
      | uu____18527 ->
          let uu____18528 = FStar_Syntax_Util.head_and_args t in
          (match uu____18528 with
           | (head1,args) ->
               let uu____18565 =
                 let uu____18566 = FStar_Syntax_Subst.compress head1 in
                 uu____18566.FStar_Syntax_Syntax.n in
               (match uu____18565 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18569,thead) ->
                    let uu____18595 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18595 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18637 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18645 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18645.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18645.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18645.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18645.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18645.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18645.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18645.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18645.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18645.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18645.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18645.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18645.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18645.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18645.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18645.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18645.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18645.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18645.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18645.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18645.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18645.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18645.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18645.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18645.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18645.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18645.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18645.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18645.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18645.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18645.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18645.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18637 with
                            | (uu____18646,ty,uu____18648) ->
                                eta_expand_with_type env t ty))
                | uu____18649 ->
                    let uu____18650 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18658 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18658.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18658.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18658.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18658.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18658.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18658.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18658.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18658.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18658.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18658.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18658.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18658.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18658.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18658.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18658.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18658.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18658.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18658.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18658.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18658.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18658.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18658.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18658.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18658.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18658.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18658.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18658.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18658.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18658.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18658.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18658.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18650 with
                     | (uu____18659,ty,uu____18661) ->
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
            | (uu____18735,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18741,FStar_Util.Inl t) ->
                let uu____18747 =
                  let uu____18750 =
                    let uu____18751 =
                      let uu____18764 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18764) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18751 in
                  FStar_Syntax_Syntax.mk uu____18750 in
                uu____18747 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18768 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18768 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18795 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18850 ->
                    let uu____18851 =
                      let uu____18860 =
                        let uu____18861 = FStar_Syntax_Subst.compress t3 in
                        uu____18861.FStar_Syntax_Syntax.n in
                      (uu____18860, tc) in
                    (match uu____18851 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18886) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18923) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____18962,FStar_Util.Inl uu____18963) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____18986 -> failwith "Impossible") in
              (match uu____18795 with
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
          let uu____19091 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19091 with
          | (univ_names1,binders1,tc) ->
              let uu____19149 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19149)
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
          let uu____19184 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19184 with
          | (univ_names1,binders1,tc) ->
              let uu____19244 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19244)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19277 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19277 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19305 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19305.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19305.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19305.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19305.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19326 = s in
          let uu____19327 =
            let uu____19328 =
              let uu____19337 = FStar_List.map (elim_uvars env) sigs in
              (uu____19337, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19328 in
          {
            FStar_Syntax_Syntax.sigel = uu____19327;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19326.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19326.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19326.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19326.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19354 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19354 with
           | (univ_names1,uu____19372,typ1) ->
               let uu___163_19386 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19386.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19386.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19386.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19386.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19392 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19392 with
           | (univ_names1,uu____19410,typ1) ->
               let uu___164_19424 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19424.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19424.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19424.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19424.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19458 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19458 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19481 =
                            let uu____19482 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19482 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19481 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___165_19485 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19485.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19485.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___166_19486 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19486.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19486.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19486.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19486.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19498 = s in
          let uu____19499 =
            let uu____19500 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19500 in
          {
            FStar_Syntax_Syntax.sigel = uu____19499;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19498.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19498.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19498.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19498.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19504 = elim_uvars_aux_t env us [] t in
          (match uu____19504 with
           | (us1,uu____19522,t1) ->
               let uu___168_19536 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19536.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19536.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19536.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19536.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19537 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19539 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19539 with
           | (univs1,binders,signature) ->
               let uu____19567 =
                 let uu____19576 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19576 with
                 | (univs_opening,univs2) ->
                     let uu____19603 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19603) in
               (match uu____19567 with
                | (univs_opening,univs_closing) ->
                    let uu____19620 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19626 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19627 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19626, uu____19627) in
                    (match uu____19620 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19649 =
                           match uu____19649 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19667 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19667 with
                                | (us1,t1) ->
                                    let uu____19678 =
                                      let uu____19683 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19690 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19683, uu____19690) in
                                    (match uu____19678 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19703 =
                                           let uu____19708 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19717 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19708, uu____19717) in
                                         (match uu____19703 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19733 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19733 in
                                              let uu____19734 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19734 with
                                               | (uu____19755,uu____19756,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19771 =
                                                       let uu____19772 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19772 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19771 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19777 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19777 with
                           | (uu____19790,uu____19791,t1) -> t1 in
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
                             | uu____19851 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19868 =
                               let uu____19869 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19869.FStar_Syntax_Syntax.n in
                             match uu____19868 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19928 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____19957 =
                               let uu____19958 =
                                 FStar_Syntax_Subst.compress t in
                               uu____19958.FStar_Syntax_Syntax.n in
                             match uu____19957 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____19979) ->
                                 let uu____20000 = destruct_action_body body in
                                 (match uu____20000 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20045 ->
                                 let uu____20046 = destruct_action_body t in
                                 (match uu____20046 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20095 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20095 with
                           | (action_univs,t) ->
                               let uu____20104 = destruct_action_typ_templ t in
                               (match uu____20104 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20145 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20145.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20145.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___170_20147 = ed in
                           let uu____20148 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20149 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20150 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20151 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20152 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20153 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20154 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20155 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20156 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20157 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20158 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20159 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20160 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20161 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20147.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20147.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20148;
                             FStar_Syntax_Syntax.bind_wp = uu____20149;
                             FStar_Syntax_Syntax.if_then_else = uu____20150;
                             FStar_Syntax_Syntax.ite_wp = uu____20151;
                             FStar_Syntax_Syntax.stronger = uu____20152;
                             FStar_Syntax_Syntax.close_wp = uu____20153;
                             FStar_Syntax_Syntax.assert_p = uu____20154;
                             FStar_Syntax_Syntax.assume_p = uu____20155;
                             FStar_Syntax_Syntax.null_wp = uu____20156;
                             FStar_Syntax_Syntax.trivial = uu____20157;
                             FStar_Syntax_Syntax.repr = uu____20158;
                             FStar_Syntax_Syntax.return_repr = uu____20159;
                             FStar_Syntax_Syntax.bind_repr = uu____20160;
                             FStar_Syntax_Syntax.actions = uu____20161
                           } in
                         let uu___171_20164 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20164.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20164.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20164.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20164.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20181 =
            match uu___88_20181 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20208 = elim_uvars_aux_t env us [] t in
                (match uu____20208 with
                 | (us1,uu____20232,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___172_20251 = sub_eff in
            let uu____20252 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20255 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20251.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20251.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20252;
              FStar_Syntax_Syntax.lift = uu____20255
            } in
          let uu___173_20258 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20258.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20258.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20258.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20258.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20268 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20268 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20302 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20302.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20302.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20302.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20302.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20313 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t