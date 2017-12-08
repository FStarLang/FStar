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
    match projectee with | Clos _0 -> true | uu____365 -> false
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
    match projectee with | Univ _0 -> true | uu____467 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____478 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___288_497  ->
    match uu___288_497 with
    | Clos (uu____498,t,uu____500,uu____501) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____546 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;
  strong: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;
        strong = __fname__strong;_} -> __fname__strong
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
    match projectee with | Arg _0 -> true | uu____782 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____818 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____854 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____911 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____953 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1009 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1049 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1081 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1127 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1173 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1198 .
    'Auu____1198 ->
      FStar_Range.range -> 'Auu____1198 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1246 = FStar_ST.op_Bang r in
      match uu____1246 with
      | FStar_Pervasives_Native.Some uu____1313 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1385 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1385 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___289_1392  ->
    match uu___289_1392 with
    | Arg (c,uu____1394,uu____1395) ->
        let uu____1396 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1396
    | MemoLazy uu____1397 -> "MemoLazy"
    | Abs (uu____1404,bs,uu____1406,uu____1407,uu____1408) ->
        let uu____1413 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1413
    | UnivArgs uu____1418 -> "UnivArgs"
    | Match uu____1425 -> "Match"
    | App (uu____1432,t,uu____1434,uu____1435) ->
        let uu____1436 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1436
    | Meta (m,uu____1438) -> "Meta"
    | Let uu____1439 -> "Let"
    | Steps (uu____1448,uu____1449,uu____1450) -> "Steps"
    | Debug (t,uu____1460) ->
        let uu____1461 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1461
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1469 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1469 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1485 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1485 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1498 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1498 then f () else ()
let is_empty: 'Auu____1502 . 'Auu____1502 Prims.list -> Prims.bool =
  fun uu___290_1508  ->
    match uu___290_1508 with | [] -> true | uu____1511 -> false
let lookup_bvar:
  'Auu____1518 'Auu____1519 .
    ('Auu____1519,'Auu____1518) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1518
  =
  fun env  ->
    fun x  ->
      try
        let uu____1543 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1543
      with
      | uu____1556 ->
          let uu____1557 =
            let uu____1558 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1558 in
          failwith uu____1557
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
          let uu____1595 =
            FStar_List.fold_left
              (fun uu____1621  ->
                 fun u1  ->
                   match uu____1621 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1646 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1646 with
                        | (k_u,n1) ->
                            let uu____1661 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1661
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1595 with
          | (uu____1679,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1705 =
                   let uu____1706 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1706 in
                 match uu____1705 with
                 | Univ u3 ->
                     ((let uu____1725 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug cfg.tcenv)
                           (FStar_Options.Other "univ_norm") in
                       if uu____1725
                       then
                         let uu____1726 =
                           FStar_Syntax_Print.univ_to_string u3 in
                         FStar_Util.print1 "Univ (in norm_universe): %s\n"
                           uu____1726
                       else ());
                      aux u3)
                 | Dummy  -> [u2]
                 | uu____1728 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1737 ->
                   let uu____1738 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1738
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1744 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1753 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1762 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1769 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1769 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1786 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1786 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1794 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1802 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1802 with
                                  | (uu____1807,m) -> n1 <= m)) in
                        if uu____1794 then rest1 else us1
                    | uu____1812 -> us1)
               | uu____1817 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1821 = aux u3 in
              FStar_List.map (fun _0_41  -> FStar_Syntax_Syntax.U_succ _0_41)
                uu____1821 in
        let uu____1824 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1824
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1826 = aux u in
           match uu____1826 with
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
          (fun uu____1930  ->
             let uu____1931 = FStar_Syntax_Print.tag_of_term t in
             let uu____1932 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1931
               uu____1932);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1939 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1941 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1966 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1967 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1968 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1969 ->
                  let uu____1986 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1986
                  then
                    let uu____1987 =
                      let uu____1988 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1989 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1988 uu____1989 in
                    failwith uu____1987
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1992 =
                    let uu____1993 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1993 in
                  mk uu____1992 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2000 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2000
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2002 = lookup_bvar env x in
                  (match uu____2002 with
                   | Univ uu____2005 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2009) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2121 = closures_as_binders_delayed cfg env bs in
                  (match uu____2121 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2149 =
                         let uu____2150 =
                           let uu____2167 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2167) in
                         FStar_Syntax_Syntax.Tm_abs uu____2150 in
                       mk uu____2149 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2198 = closures_as_binders_delayed cfg env bs in
                  (match uu____2198 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2240 =
                    let uu____2251 =
                      let uu____2258 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2258] in
                    closures_as_binders_delayed cfg env uu____2251 in
                  (match uu____2240 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2276 =
                         let uu____2277 =
                           let uu____2284 =
                             let uu____2285 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2285
                               FStar_Pervasives_Native.fst in
                           (uu____2284, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2277 in
                       mk uu____2276 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2376 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2376
                    | FStar_Util.Inr c ->
                        let uu____2390 = close_comp cfg env c in
                        FStar_Util.Inr uu____2390 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2406 =
                    let uu____2407 =
                      let uu____2434 = closure_as_term_delayed cfg env t11 in
                      (uu____2434, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2407 in
                  mk uu____2406 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2485 =
                    let uu____2486 =
                      let uu____2493 = closure_as_term_delayed cfg env t' in
                      let uu____2496 =
                        let uu____2497 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2497 in
                      (uu____2493, uu____2496) in
                    FStar_Syntax_Syntax.Tm_meta uu____2486 in
                  mk uu____2485 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2557 =
                    let uu____2558 =
                      let uu____2565 = closure_as_term_delayed cfg env t' in
                      let uu____2568 =
                        let uu____2569 =
                          let uu____2576 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2576) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2569 in
                      (uu____2565, uu____2568) in
                    FStar_Syntax_Syntax.Tm_meta uu____2558 in
                  mk uu____2557 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2595 =
                    let uu____2596 =
                      let uu____2603 = closure_as_term_delayed cfg env t' in
                      let uu____2606 =
                        let uu____2607 =
                          let uu____2616 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2616) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2607 in
                      (uu____2603, uu____2606) in
                    FStar_Syntax_Syntax.Tm_meta uu____2596 in
                  mk uu____2595 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2629 =
                    let uu____2630 =
                      let uu____2637 = closure_as_term_delayed cfg env t' in
                      (uu____2637, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2630 in
                  mk uu____2629 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2677  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2696 =
                    let uu____2707 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2707
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2726 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___309_2738 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___309_2738.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___309_2738.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2726)) in
                  (match uu____2696 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___310_2754 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___310_2754.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___310_2754.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2765,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2824  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2849 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2849
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2869  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2891 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2891
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___311_2903 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___311_2903.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___311_2903.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_42  -> FStar_Util.Inl _0_42)) in
                    let uu___312_2904 = lb in
                    let uu____2905 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___312_2904.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___312_2904.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2905
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2935  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3024 =
                    match uu____3024 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3079 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3100 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3160  ->
                                        fun uu____3161  ->
                                          match (uu____3160, uu____3161) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3252 =
                                                norm_pat env3 p1 in
                                              (match uu____3252 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3100 with
                               | (pats1,env3) ->
                                   ((let uu___313_3334 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___313_3334.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___314_3353 = x in
                                let uu____3354 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___314_3353.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___314_3353.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3354
                                } in
                              ((let uu___315_3368 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___315_3368.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___316_3379 = x in
                                let uu____3380 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___316_3379.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___316_3379.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3380
                                } in
                              ((let uu___317_3394 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___317_3394.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___318_3410 = x in
                                let uu____3411 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___318_3410.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___318_3410.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3411
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___319_3418 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___319_3418.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3421 = norm_pat env1 pat in
                        (match uu____3421 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3450 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3450 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3456 =
                    let uu____3457 =
                      let uu____3480 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3480) in
                    FStar_Syntax_Syntax.Tm_match uu____3457 in
                  mk uu____3456 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3566 -> closure_as_term cfg env t
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
        | uu____3592 ->
            FStar_List.map
              (fun uu____3609  ->
                 match uu____3609 with
                 | (x,imp) ->
                     let uu____3628 = closure_as_term_delayed cfg env x in
                     (uu____3628, imp)) args
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
        let uu____3642 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3691  ->
                  fun uu____3692  ->
                    match (uu____3691, uu____3692) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___320_3762 = b in
                          let uu____3763 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___320_3762.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___320_3762.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3763
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3642 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3856 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3869 = closure_as_term_delayed cfg env t in
                 let uu____3870 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3869 uu____3870
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3883 = closure_as_term_delayed cfg env t in
                 let uu____3884 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3883 uu____3884
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___291_3910  ->
                           match uu___291_3910 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3914 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3914
                           | f -> f)) in
                 let uu____3918 =
                   let uu___321_3919 = c1 in
                   let uu____3920 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3920;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___321_3919.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3918)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___292_3930  ->
            match uu___292_3930 with
            | FStar_Syntax_Syntax.DECREASES uu____3931 -> false
            | uu____3934 -> true))
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
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___293_3952  ->
                      match uu___293_3952 with
                      | FStar_Syntax_Syntax.DECREASES uu____3953 -> false
                      | uu____3956 -> true)) in
            let rc1 =
              let uu___322_3958 = rc in
              let uu____3959 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___322_3958.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3959;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3966 -> lopt
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
    let uu____4054 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4054 in
  let arg_as_bounded_int uu____4082 =
    match uu____4082 with
    | (a,uu____4094) ->
        let uu____4101 =
          let uu____4102 = FStar_Syntax_Subst.compress a in
          uu____4102.FStar_Syntax_Syntax.n in
        (match uu____4101 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4112;
                FStar_Syntax_Syntax.vars = uu____4113;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4115;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4116;_},uu____4117)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4156 =
               let uu____4161 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4161) in
             FStar_Pervasives_Native.Some uu____4156
         | uu____4166 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4208 = f a in FStar_Pervasives_Native.Some uu____4208
    | uu____4209 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4259 = f a0 a1 in FStar_Pervasives_Native.Some uu____4259
    | uu____4260 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4309 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4309 in
  let binary_op as_a f res args =
    let uu____4365 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4365 in
  let as_primitive_step uu____4389 =
    match uu____4389 with
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
           let uu____4437 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4437) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4465 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4465) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4486 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4486) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4514 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4514) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4542 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4542) in
  let list_of_string' rng s =
    let name l =
      let uu____4556 =
        let uu____4557 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4557 in
      mk uu____4556 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4567 =
      let uu____4570 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4570 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4567 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4600 =
      let uu____4601 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4601 in
    FStar_Syntax_Embeddings.embed_int rng uu____4600 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4619 = arg_as_string a1 in
        (match uu____4619 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4625 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4625 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4638 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4638
              | uu____4639 -> FStar_Pervasives_Native.None)
         | uu____4644 -> FStar_Pervasives_Native.None)
    | uu____4647 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4657 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4657 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4681 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4692 =
          let uu____4713 = arg_as_string fn in
          let uu____4716 = arg_as_int from_line in
          let uu____4719 = arg_as_int from_col in
          let uu____4722 = arg_as_int to_line in
          let uu____4725 = arg_as_int to_col in
          (uu____4713, uu____4716, uu____4719, uu____4722, uu____4725) in
        (match uu____4692 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4756 =
                 let uu____4757 = FStar_BigInt.to_int_fs from_l in
                 let uu____4758 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4757 uu____4758 in
               let uu____4759 =
                 let uu____4760 = FStar_BigInt.to_int_fs to_l in
                 let uu____4761 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4760 uu____4761 in
               FStar_Range.mk_range fn1 uu____4756 uu____4759 in
             let uu____4762 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4762
         | uu____4767 -> FStar_Pervasives_Native.None)
    | uu____4788 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4815)::(a1,uu____4817)::(a2,uu____4819)::[] ->
        let uu____4856 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4856 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4869 -> FStar_Pervasives_Native.None)
    | uu____4870 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4897)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4906 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____4930 =
      let uu____4945 =
        let uu____4960 =
          let uu____4975 =
            let uu____4990 =
              let uu____5005 =
                let uu____5020 =
                  let uu____5035 =
                    let uu____5050 =
                      let uu____5065 =
                        let uu____5080 =
                          let uu____5095 =
                            let uu____5110 =
                              let uu____5125 =
                                let uu____5140 =
                                  let uu____5155 =
                                    let uu____5170 =
                                      let uu____5185 =
                                        let uu____5200 =
                                          let uu____5215 =
                                            let uu____5228 =
                                              FStar_Parser_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____5228,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____5235 =
                                            let uu____5250 =
                                              let uu____5263 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____5263,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list
                                                      FStar_Syntax_Embeddings.unembed_char_safe)
                                                   string_of_list')) in
                                            let uu____5272 =
                                              let uu____5287 =
                                                let uu____5302 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____5302,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              let uu____5311 =
                                                let uu____5328 =
                                                  let uu____5343 =
                                                    FStar_Parser_Const.p2l
                                                      ["Prims"; "mk_range"] in
                                                  (uu____5343,
                                                    (Prims.parse_int "5"),
                                                    mk_range1) in
                                                let uu____5352 =
                                                  let uu____5369 =
                                                    let uu____5388 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "Range";
                                                        "prims_to_fstar_range"] in
                                                    (uu____5388,
                                                      (Prims.parse_int "1"),
                                                      idstep) in
                                                  [uu____5369] in
                                                uu____5328 :: uu____5352 in
                                              uu____5287 :: uu____5311 in
                                            uu____5250 :: uu____5272 in
                                          uu____5215 :: uu____5235 in
                                        (FStar_Parser_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____5200 in
                                      (FStar_Parser_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____5185 in
                                    (FStar_Parser_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____5170 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____5155 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____5140 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5125 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5110 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5095 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5080 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5065 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5724 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5724)))
                      :: uu____5050 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5750 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5750)))
                    :: uu____5035 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5776 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5776)))
                  :: uu____5020 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5802 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5802)))
                :: uu____5005 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____4990 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____4975 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____4960 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____4945 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____4930 in
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
      let uu____5952 =
        let uu____5953 =
          let uu____5954 = FStar_Syntax_Syntax.as_arg c in [uu____5954] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5953 in
      uu____5952 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____5989 =
              let uu____6002 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6002, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6022  ->
                        fun uu____6023  ->
                          match (uu____6022, uu____6023) with
                          | ((int_to_t1,x),(uu____6042,y)) ->
                              let uu____6052 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6052))) in
            let uu____6053 =
              let uu____6068 =
                let uu____6081 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6081, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6101  ->
                          fun uu____6102  ->
                            match (uu____6101, uu____6102) with
                            | ((int_to_t1,x),(uu____6121,y)) ->
                                let uu____6131 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6131))) in
              let uu____6132 =
                let uu____6147 =
                  let uu____6160 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6160, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6180  ->
                            fun uu____6181  ->
                              match (uu____6180, uu____6181) with
                              | ((int_to_t1,x),(uu____6200,y)) ->
                                  let uu____6210 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6210))) in
                [uu____6147] in
              uu____6068 :: uu____6132 in
            uu____5989 :: uu____6053)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6300)::(a1,uu____6302)::(a2,uu____6304)::[] ->
        let uu____6341 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6341 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___323_6347 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___323_6347.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___323_6347.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___324_6351 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___324_6351.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___324_6351.FStar_Syntax_Syntax.vars)
                })
         | uu____6352 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6354)::uu____6355::(a1,uu____6357)::(a2,uu____6359)::[] ->
        let uu____6408 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6408 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___323_6414 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___323_6414.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___323_6414.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___324_6418 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___324_6418.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___324_6418.FStar_Syntax_Syntax.vars)
                })
         | uu____6419 -> FStar_Pervasives_Native.None)
    | uu____6420 -> failwith "Unexpected number of arguments" in
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
      let uu____6439 =
        let uu____6440 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6440 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6439
    with | uu____6446 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6450 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6450) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6510  ->
           fun subst1  ->
             match uu____6510 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6552)) ->
                      let uu____6611 = b in
                      (match uu____6611 with
                       | (bv,uu____6619) ->
                           let uu____6620 =
                             let uu____6621 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6621 in
                           if uu____6620
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6626 = unembed_binder term1 in
                              match uu____6626 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6633 =
                                      let uu___327_6634 = bv in
                                      let uu____6635 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___327_6634.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___327_6634.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6635
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6633 in
                                  let b_for_x =
                                    let uu____6639 =
                                      let uu____6646 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6646) in
                                    FStar_Syntax_Syntax.NT uu____6639 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___294_6655  ->
                                         match uu___294_6655 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6656,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6658;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6659;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6664 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6665 -> subst1)) env []
let reduce_primops:
  'Auu____6682 'Auu____6683 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6683) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6682 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____6724 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6724
          then tm
          else
            (let uu____6726 = FStar_Syntax_Util.head_and_args tm in
             match uu____6726 with
             | (head1,args) ->
                 let uu____6763 =
                   let uu____6764 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6764.FStar_Syntax_Syntax.n in
                 (match uu____6763 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6768 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6768 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6785  ->
                                   let uu____6786 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6787 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6794 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6786 uu____6787 uu____6794);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6799  ->
                                   let uu____6800 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6800);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6803  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6805 =
                                 prim_step.interpretation psc args in
                               match uu____6805 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6811  ->
                                         let uu____6812 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6812);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6818  ->
                                         let uu____6819 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6820 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6819 uu____6820);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6821 ->
                           (log_primops cfg
                              (fun uu____6825  ->
                                 let uu____6826 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6826);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6830  ->
                            let uu____6831 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6831);
                       (match args with
                        | (a1,uu____6833)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6850 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6862  ->
                            let uu____6863 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6863);
                       (match args with
                        | (a1,uu____6865)::(a2,uu____6867)::[] ->
                            let uu____6894 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____6894 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___328_6898 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___328_6898.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___328_6898.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6901 -> tm))
                  | uu____6910 -> tm))
let reduce_equality:
  'Auu____6915 'Auu____6916 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6916) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6915 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___329_6954 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___329_6954.tcenv);
           delta_level = (uu___329_6954.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___329_6954.strong)
         }) tm
let maybe_simplify:
  'Auu____6961 'Auu____6962 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6962) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6961 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7004 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7004
          then tm1
          else
            (let w t =
               let uu___330_7016 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___330_7016.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___330_7016.FStar_Syntax_Syntax.vars)
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
               | uu____7033 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7073;
                         FStar_Syntax_Syntax.vars = uu____7074;_},uu____7075);
                    FStar_Syntax_Syntax.pos = uu____7076;
                    FStar_Syntax_Syntax.vars = uu____7077;_},args)
                 ->
                 let uu____7103 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7103
                 then
                   let uu____7104 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7104 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7159)::
                        (uu____7160,(arg,uu____7162))::[] -> arg
                    | (uu____7227,(arg,uu____7229))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7230)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7295)::uu____7296::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7359::(FStar_Pervasives_Native.Some (false
                                   ),uu____7360)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7423 -> tm1)
                 else
                   (let uu____7439 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7439
                    then
                      let uu____7440 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7440 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7495)::uu____7496::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7559::(FStar_Pervasives_Native.Some (true
                                     ),uu____7560)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7623)::
                          (uu____7624,(arg,uu____7626))::[] -> arg
                      | (uu____7691,(arg,uu____7693))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7694)::[]
                          -> arg
                      | uu____7759 -> tm1
                    else
                      (let uu____7775 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7775
                       then
                         let uu____7776 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7776 with
                         | uu____7831::(FStar_Pervasives_Native.Some (true
                                        ),uu____7832)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____7895)::uu____7896::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____7959)::
                             (uu____7960,(arg,uu____7962))::[] -> arg
                         | (uu____8027,(p,uu____8029))::(uu____8030,(q,uu____8032))::[]
                             ->
                             let uu____8097 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8097
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8099 -> tm1
                       else
                         (let uu____8115 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8115
                          then
                            let uu____8116 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8116 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8171)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8210)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8249 -> tm1
                          else
                            (let uu____8265 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8265
                             then
                               match args with
                               | (t,uu____8267)::[] ->
                                   let uu____8284 =
                                     let uu____8285 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8285.FStar_Syntax_Syntax.n in
                                   (match uu____8284 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8288::[],body,uu____8290) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8317 -> tm1)
                                    | uu____8320 -> tm1)
                               | (uu____8321,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8322))::
                                   (t,uu____8324)::[] ->
                                   let uu____8363 =
                                     let uu____8364 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8364.FStar_Syntax_Syntax.n in
                                   (match uu____8363 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8367::[],body,uu____8369) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8396 -> tm1)
                                    | uu____8399 -> tm1)
                               | uu____8400 -> tm1
                             else
                               (let uu____8410 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8410
                                then
                                  match args with
                                  | (t,uu____8412)::[] ->
                                      let uu____8429 =
                                        let uu____8430 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8430.FStar_Syntax_Syntax.n in
                                      (match uu____8429 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8433::[],body,uu____8435)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8462 -> tm1)
                                       | uu____8465 -> tm1)
                                  | (uu____8466,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8467))::(t,uu____8469)::[] ->
                                      let uu____8508 =
                                        let uu____8509 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8509.FStar_Syntax_Syntax.n in
                                      (match uu____8508 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8512::[],body,uu____8514)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8541 -> tm1)
                                       | uu____8544 -> tm1)
                                  | uu____8545 -> tm1
                                else
                                  (let uu____8555 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8555
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8556;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8557;_},uu____8558)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8575;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8576;_},uu____8577)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8594 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8605;
                    FStar_Syntax_Syntax.vars = uu____8606;_},args)
                 ->
                 let uu____8628 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8628
                 then
                   let uu____8629 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8629 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8684)::
                        (uu____8685,(arg,uu____8687))::[] -> arg
                    | (uu____8752,(arg,uu____8754))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8755)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8820)::uu____8821::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8884::(FStar_Pervasives_Native.Some (false
                                   ),uu____8885)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8948 -> tm1)
                 else
                   (let uu____8964 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8964
                    then
                      let uu____8965 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8965 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9020)::uu____9021::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9084::(FStar_Pervasives_Native.Some (true
                                     ),uu____9085)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9148)::
                          (uu____9149,(arg,uu____9151))::[] -> arg
                      | (uu____9216,(arg,uu____9218))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9219)::[]
                          -> arg
                      | uu____9284 -> tm1
                    else
                      (let uu____9300 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9300
                       then
                         let uu____9301 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9301 with
                         | uu____9356::(FStar_Pervasives_Native.Some (true
                                        ),uu____9357)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9420)::uu____9421::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9484)::
                             (uu____9485,(arg,uu____9487))::[] -> arg
                         | (uu____9552,(p,uu____9554))::(uu____9555,(q,uu____9557))::[]
                             ->
                             let uu____9622 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9622
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9624 -> tm1
                       else
                         (let uu____9640 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9640
                          then
                            let uu____9641 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9641 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9696)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9735)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9774 -> tm1
                          else
                            (let uu____9790 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9790
                             then
                               match args with
                               | (t,uu____9792)::[] ->
                                   let uu____9809 =
                                     let uu____9810 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9810.FStar_Syntax_Syntax.n in
                                   (match uu____9809 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9813::[],body,uu____9815) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9842 -> tm1)
                                    | uu____9845 -> tm1)
                               | (uu____9846,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9847))::
                                   (t,uu____9849)::[] ->
                                   let uu____9888 =
                                     let uu____9889 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9889.FStar_Syntax_Syntax.n in
                                   (match uu____9888 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9892::[],body,uu____9894) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9921 -> tm1)
                                    | uu____9924 -> tm1)
                               | uu____9925 -> tm1
                             else
                               (let uu____9935 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9935
                                then
                                  match args with
                                  | (t,uu____9937)::[] ->
                                      let uu____9954 =
                                        let uu____9955 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9955.FStar_Syntax_Syntax.n in
                                      (match uu____9954 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9958::[],body,uu____9960)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9987 -> tm1)
                                       | uu____9990 -> tm1)
                                  | (uu____9991,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9992))::(t,uu____9994)::[] ->
                                      let uu____10033 =
                                        let uu____10034 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10034.FStar_Syntax_Syntax.n in
                                      (match uu____10033 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10037::[],body,uu____10039)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10066 -> tm1)
                                       | uu____10069 -> tm1)
                                  | uu____10070 -> tm1
                                else
                                  (let uu____10080 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10080
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10081;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10082;_},uu____10083)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10100;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10101;_},uu____10102)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10119 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | uu____10129 -> tm1)
let is_norm_request:
  'Auu____10133 .
    FStar_Syntax_Syntax.term -> 'Auu____10133 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10146 =
        let uu____10153 =
          let uu____10154 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10154.FStar_Syntax_Syntax.n in
        (uu____10153, args) in
      match uu____10146 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10160::uu____10161::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10165::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10170::uu____10171::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10174 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___295_10185  ->
    match uu___295_10185 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10191 =
          let uu____10194 =
            let uu____10195 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10195 in
          [uu____10194] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10191
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10210 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10210) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10248 =
          let uu____10251 =
            let uu____10256 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10256 s in
          FStar_All.pipe_right uu____10251 FStar_Util.must in
        FStar_All.pipe_right uu____10248 tr_norm_steps in
      match args with
      | uu____10281::(tm,uu____10283)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10306)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10321)::uu____10322::(tm,uu____10324)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10364 =
              let uu____10367 = full_norm steps in parse_steps uu____10367 in
            Beta :: uu____10364 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10376 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___296_10393  ->
    match uu___296_10393 with
    | (App
        (uu____10396,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10397;
                       FStar_Syntax_Syntax.vars = uu____10398;_},uu____10399,uu____10400))::uu____10401
        -> true
    | uu____10408 -> false
let firstn:
  'Auu____10414 .
    Prims.int ->
      'Auu____10414 Prims.list ->
        ('Auu____10414 Prims.list,'Auu____10414 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack1  ->
      match stack1 with
      | (App
          (uu____10450,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10451;
                         FStar_Syntax_Syntax.vars = uu____10452;_},uu____10453,uu____10454))::uu____10455
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10462 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10578  ->
               let uu____10579 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10580 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10581 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10588 =
                 let uu____10589 =
                   let uu____10592 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10592 in
                 stack_to_string uu____10589 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10579 uu____10580 uu____10581 uu____10588);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10615 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10640 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10657 =
                 let uu____10658 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10659 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10658 uu____10659 in
               failwith uu____10657
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10660 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10677 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10678 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10679;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10680;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10683;
                 FStar_Syntax_Syntax.fv_delta = uu____10684;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10685;
                 FStar_Syntax_Syntax.fv_delta = uu____10686;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10687);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10695 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10695 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10701  ->
                     let uu____10702 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10703 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10702 uu____10703);
                if b
                then
                  (let uu____10704 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10704 t1 fv)
                else rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___331_10743 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___331_10743.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___331_10743.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10776 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10776) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___332_10784 = cfg in
                 let uu____10785 =
                   FStar_List.filter
                     (fun uu___297_10788  ->
                        match uu___297_10788 with
                        | UnfoldOnly uu____10789 -> false
                        | NoDeltaSteps  -> false
                        | uu____10792 -> true) cfg.steps in
                 {
                   steps = uu____10785;
                   tcenv = (uu___332_10784.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___332_10784.primitive_steps);
                   strong = (uu___332_10784.strong)
                 } in
               let uu____10793 = get_norm_request (norm cfg' env []) args in
               (match uu____10793 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10809 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___298_10814  ->
                                match uu___298_10814 with
                                | UnfoldUntil uu____10815 -> true
                                | UnfoldOnly uu____10816 -> true
                                | uu____10819 -> false)) in
                      if uu____10809
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___333_10824 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___333_10824.tcenv);
                        delta_level;
                        primitive_steps = (uu___333_10824.primitive_steps);
                        strong = (uu___333_10824.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10835 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10835
                      then
                        let uu____10838 =
                          let uu____10839 =
                            let uu____10844 = FStar_Util.now () in
                            (t1, uu____10844) in
                          Debug uu____10839 in
                        uu____10838 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____10846;
                  FStar_Syntax_Syntax.vars = uu____10847;_},a1::a2::rest)
               ->
               let uu____10895 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10895 with
                | (hd1,uu____10911) ->
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
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10976;
                  FStar_Syntax_Syntax.vars = uu____10977;_},a1::a2::rest)
               ->
               let uu____11025 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11025 with
                | (hd1,uu____11041) ->
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
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of );
                  FStar_Syntax_Syntax.pos = uu____11106;
                  FStar_Syntax_Syntax.vars = uu____11107;_},a1::a2::a3::rest)
               ->
               let uu____11168 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11168 with
                | (hd1,uu____11184) ->
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
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____11255);
                  FStar_Syntax_Syntax.pos = uu____11256;
                  FStar_Syntax_Syntax.vars = uu____11257;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11289 = FStar_List.tl stack1 in
               norm cfg env uu____11289 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11292;
                  FStar_Syntax_Syntax.vars = uu____11293;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11325 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11325 with
                | (reify_head,uu____11341) ->
                    let a1 =
                      let uu____11363 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11363 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11366);
                            FStar_Syntax_Syntax.pos = uu____11367;
                            FStar_Syntax_Syntax.vars = uu____11368;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11402 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11412 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11412
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11419 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11419
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11422 =
                      let uu____11429 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11429, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11422 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___299_11442  ->
                         match uu___299_11442 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11445 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     (((((((((FStar_Syntax_Syntax.fv_eq_lid f
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
                            FStar_Parser_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Parser_Const.false_lid)) in
                 if uu____11445
                 then false
                 else
                   (let uu____11447 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___300_11454  ->
                              match uu___300_11454 with
                              | UnfoldOnly uu____11455 -> true
                              | uu____11458 -> false)) in
                    match uu____11447 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11462 -> should_delta) in
               (log cfg
                  (fun uu____11470  ->
                     let uu____11471 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11472 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11473 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11471 uu____11472 uu____11473);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11476 = lookup_bvar env x in
               (match uu____11476 with
                | Univ uu____11479 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11528 = FStar_ST.op_Bang r in
                      (match uu____11528 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11665  ->
                                 let uu____11666 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11667 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11666
                                   uu____11667);
                            (let uu____11668 =
                               let uu____11669 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11669.FStar_Syntax_Syntax.n in
                             match uu____11668 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11672 ->
                                 norm cfg env2 stack1 t'
                             | uu____11689 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11747)::uu____11748 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11757)::uu____11758 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11768,uu____11769))::stack_rest ->
                    (match c with
                     | Univ uu____11773 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11782 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11803  ->
                                    let uu____11804 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11804);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11844  ->
                                    let uu____11845 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11845);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___334_11895 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___334_11895.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___334_11895.strong)
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11928  ->
                          let uu____11929 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11929);
                     norm cfg env stack2 t1)
                | (Debug uu____11930)::uu____11931 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11938 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11938
                    else
                      (let uu____11940 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11940 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11982  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12010 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12010
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12020 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12020)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12025 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12025.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12025.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12026 -> lopt in
                           (log cfg
                              (fun uu____12032  ->
                                 let uu____12033 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12033);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12046 = cfg in
                               {
                                 steps = (uu___336_12046.steps);
                                 tcenv = (uu___336_12046.tcenv);
                                 delta_level = (uu___336_12046.delta_level);
                                 primitive_steps =
                                   (uu___336_12046.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12057)::uu____12058 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12065 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12065
                    else
                      (let uu____12067 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12067 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12109  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12137 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12137
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12147 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12147)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12152 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12152.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12152.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12153 -> lopt in
                           (log cfg
                              (fun uu____12159  ->
                                 let uu____12160 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12160);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12173 = cfg in
                               {
                                 steps = (uu___336_12173.steps);
                                 tcenv = (uu___336_12173.tcenv);
                                 delta_level = (uu___336_12173.delta_level);
                                 primitive_steps =
                                   (uu___336_12173.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12184)::uu____12185 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12196 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12196
                    else
                      (let uu____12198 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12198 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12240  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12268 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12268
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12278 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12278)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12283 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12283.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12283.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12284 -> lopt in
                           (log cfg
                              (fun uu____12290  ->
                                 let uu____12291 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12291);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12304 = cfg in
                               {
                                 steps = (uu___336_12304.steps);
                                 tcenv = (uu___336_12304.tcenv);
                                 delta_level = (uu___336_12304.delta_level);
                                 primitive_steps =
                                   (uu___336_12304.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12315)::uu____12316 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12327 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12327
                    else
                      (let uu____12329 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12329 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12371  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12399 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12399
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12409 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12409)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12414 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12414.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12414.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12415 -> lopt in
                           (log cfg
                              (fun uu____12421  ->
                                 let uu____12422 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12422);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12435 = cfg in
                               {
                                 steps = (uu___336_12435.steps);
                                 tcenv = (uu___336_12435.tcenv);
                                 delta_level = (uu___336_12435.delta_level);
                                 primitive_steps =
                                   (uu___336_12435.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12446)::uu____12447 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12462 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12462
                    else
                      (let uu____12464 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12464 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12506  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12534 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12534
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12544 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12544)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12549 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12549.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12549.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12550 -> lopt in
                           (log cfg
                              (fun uu____12556  ->
                                 let uu____12557 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12557);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12570 = cfg in
                               {
                                 steps = (uu___336_12570.steps);
                                 tcenv = (uu___336_12570.tcenv);
                                 delta_level = (uu___336_12570.delta_level);
                                 primitive_steps =
                                   (uu___336_12570.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12581 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12581
                    else
                      (let uu____12583 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12583 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12625  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12653 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12653
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12663 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12663)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12668 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12668.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12668.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12669 -> lopt in
                           (log cfg
                              (fun uu____12675  ->
                                 let uu____12676 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12676);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12689 = cfg in
                               {
                                 steps = (uu___336_12689.steps);
                                 tcenv = (uu___336_12689.tcenv);
                                 delta_level = (uu___336_12689.delta_level);
                                 primitive_steps =
                                   (uu___336_12689.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12738  ->
                         fun stack2  ->
                           match uu____12738 with
                           | (a,aq) ->
                               let uu____12750 =
                                 let uu____12751 =
                                   let uu____12758 =
                                     let uu____12759 =
                                       let uu____12790 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12790, false) in
                                     Clos uu____12759 in
                                   (uu____12758, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12751 in
                               uu____12750 :: stack2) args) in
               (log cfg
                  (fun uu____12866  ->
                     let uu____12867 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12867);
                norm cfg env stack2 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains Weak cfg.steps
               then
                 (match (env, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___337_12903 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___337_12903.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___337_12903.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12904 ->
                      let uu____12909 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12909)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12912 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12912 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12943 =
                          let uu____12944 =
                            let uu____12951 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___338_12953 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___338_12953.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___338_12953.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12951) in
                          FStar_Syntax_Syntax.Tm_refine uu____12944 in
                        mk uu____12943 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12972 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12972
               else
                 (let uu____12974 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12974 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12982 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13006  -> dummy :: env1) env) in
                        norm_comp cfg uu____12982 c1 in
                      let t2 =
                        let uu____13028 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13028 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13087)::uu____13088 ->
                    (log cfg
                       (fun uu____13099  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13100)::uu____13101 ->
                    (log cfg
                       (fun uu____13112  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13113,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13114;
                                   FStar_Syntax_Syntax.vars = uu____13115;_},uu____13116,uu____13117))::uu____13118
                    ->
                    (log cfg
                       (fun uu____13127  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13128)::uu____13129 ->
                    (log cfg
                       (fun uu____13140  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13141 ->
                    (log cfg
                       (fun uu____13144  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13148  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13165 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13165
                         | FStar_Util.Inr c ->
                             let uu____13173 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13173 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13179 =
                         let uu____13180 =
                           let uu____13181 =
                             let uu____13208 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13208, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13181 in
                         mk uu____13180 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13179))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13284,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13285;
                               FStar_Syntax_Syntax.lbunivs = uu____13286;
                               FStar_Syntax_Syntax.lbtyp = uu____13287;
                               FStar_Syntax_Syntax.lbeff = uu____13288;
                               FStar_Syntax_Syntax.lbdef = uu____13289;_}::uu____13290),uu____13291)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13327 =
                 (let uu____13330 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13330) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13332 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13332))) in
               if uu____13327
               then
                 let binder =
                   let uu____13334 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13334 in
                 let env1 =
                   let uu____13344 =
                     let uu____13351 =
                       let uu____13352 =
                         let uu____13383 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13383,
                           false) in
                       Clos uu____13352 in
                     ((FStar_Pervasives_Native.Some binder), uu____13351) in
                   uu____13344 :: env in
                 (log cfg
                    (fun uu____13468  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13470 =
                    let uu____13475 =
                      let uu____13476 =
                        let uu____13477 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13477
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13476] in
                    FStar_Syntax_Subst.open_term uu____13475 body in
                  match uu____13470 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13486  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13494 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13494 in
                          FStar_Util.Inl
                            (let uu___339_13504 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___339_13504.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___339_13504.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13507  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___340_13509 = lb in
                           let uu____13510 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___340_13509.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___340_13509.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13510
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13545  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___341_13565 = cfg in
                           {
                             steps = (uu___341_13565.steps);
                             tcenv = (uu___341_13565.tcenv);
                             delta_level = (uu___341_13565.delta_level);
                             primitive_steps =
                               (uu___341_13565.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13568  ->
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
               let uu____13585 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13585 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13621 =
                               let uu___342_13622 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___342_13622.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___342_13622.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13621 in
                           let uu____13623 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13623 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13649 =
                                   FStar_List.map (fun uu____13665  -> dummy)
                                     lbs1 in
                                 let uu____13666 =
                                   let uu____13675 =
                                     FStar_List.map
                                       (fun uu____13695  -> dummy) xs1 in
                                   FStar_List.append uu____13675 env in
                                 FStar_List.append uu____13649 uu____13666 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13719 =
                                       let uu___343_13720 = rc in
                                       let uu____13721 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___343_13720.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13721;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___343_13720.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13719
                                 | uu____13728 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___344_13732 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___344_13732.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___344_13732.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13742 =
                        FStar_List.map (fun uu____13758  -> dummy) lbs2 in
                      FStar_List.append uu____13742 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13766 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13766 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___345_13782 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___345_13782.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___345_13782.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13809 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13809
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13828 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13904  ->
                        match uu____13904 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___346_14025 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___346_14025.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___346_14025.FStar_Syntax_Syntax.sort)
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
               (match uu____13828 with
                | (rec_env,memos,uu____14222) ->
                    let uu____14275 =
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
                             let uu____14806 =
                               let uu____14813 =
                                 let uu____14814 =
                                   let uu____14845 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14845, false) in
                                 Clos uu____14814 in
                               (FStar_Pervasives_Native.None, uu____14813) in
                             uu____14806 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14950 =
                      let uu____14951 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14951 in
                    if uu____14950
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14961 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14961
                        then
                          let uu___347_14962 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___347_14962.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___347_14962.primitive_steps);
                            strong = (uu___347_14962.strong)
                          }
                        else
                          (let uu___348_14964 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___348_14964.tcenv);
                             delta_level = (uu___348_14964.delta_level);
                             primitive_steps =
                               (uu___348_14964.primitive_steps);
                             strong = (uu___348_14964.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14966 =
                         let uu____14967 = FStar_Syntax_Subst.compress head1 in
                         uu____14967.FStar_Syntax_Syntax.n in
                       match uu____14966 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14985 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14985 with
                            | (uu____14986,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14992 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15000 =
                                         let uu____15001 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15001.FStar_Syntax_Syntax.n in
                                       match uu____15000 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15007,uu____15008))
                                           ->
                                           let uu____15017 =
                                             let uu____15018 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15018.FStar_Syntax_Syntax.n in
                                           (match uu____15017 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15024,msrc,uu____15026))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15035 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15035
                                            | uu____15036 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15037 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15038 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15038 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___349_15043 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___349_15043.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___349_15043.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___349_15043.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15044 =
                                            FStar_List.tl stack1 in
                                          let uu____15045 =
                                            let uu____15046 =
                                              let uu____15049 =
                                                let uu____15050 =
                                                  let uu____15063 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15063) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15050 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15049 in
                                            uu____15046
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15044
                                            uu____15045
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15079 =
                                            let uu____15080 = is_return body in
                                            match uu____15080 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15084;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15085;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15090 -> false in
                                          if uu____15079
                                          then
                                            norm cfg env stack1
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
                                               let uu____15114 =
                                                 let uu____15117 =
                                                   let uu____15118 =
                                                     let uu____15135 =
                                                       let uu____15138 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15138] in
                                                     (uu____15135, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15118 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15117 in
                                               uu____15114
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15154 =
                                                 let uu____15155 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15155.FStar_Syntax_Syntax.n in
                                               match uu____15154 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15161::uu____15162::[])
                                                   ->
                                                   let uu____15169 =
                                                     let uu____15172 =
                                                       let uu____15173 =
                                                         let uu____15180 =
                                                           let uu____15183 =
                                                             let uu____15184
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15184 in
                                                           let uu____15185 =
                                                             let uu____15188
                                                               =
                                                               let uu____15189
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15189 in
                                                             [uu____15188] in
                                                           uu____15183 ::
                                                             uu____15185 in
                                                         (bind1, uu____15180) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15173 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15172 in
                                                   uu____15169
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15197 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15203 =
                                                 let uu____15206 =
                                                   let uu____15207 =
                                                     let uu____15222 =
                                                       let uu____15225 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15226 =
                                                         let uu____15229 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15230 =
                                                           let uu____15233 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15234 =
                                                             let uu____15237
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15238
                                                               =
                                                               let uu____15241
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15242
                                                                 =
                                                                 let uu____15245
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15245] in
                                                               uu____15241 ::
                                                                 uu____15242 in
                                                             uu____15237 ::
                                                               uu____15238 in
                                                           uu____15233 ::
                                                             uu____15234 in
                                                         uu____15229 ::
                                                           uu____15230 in
                                                       uu____15225 ::
                                                         uu____15226 in
                                                     (bind_inst, uu____15222) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15207 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15206 in
                                               uu____15203
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15253 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15253 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15277 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15277 with
                            | (uu____15278,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15313 =
                                        let uu____15314 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15314.FStar_Syntax_Syntax.n in
                                      match uu____15313 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15320) -> t4
                                      | uu____15325 -> head2 in
                                    let uu____15326 =
                                      let uu____15327 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15327.FStar_Syntax_Syntax.n in
                                    match uu____15326 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15333 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15334 = maybe_extract_fv head2 in
                                  match uu____15334 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15344 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15344
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15349 =
                                          maybe_extract_fv head3 in
                                        match uu____15349 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15354 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15355 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15360 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15375 =
                                    match uu____15375 with
                                    | (e,q) ->
                                        let uu____15382 =
                                          let uu____15383 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15383.FStar_Syntax_Syntax.n in
                                        (match uu____15382 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15398 -> false) in
                                  let uu____15399 =
                                    let uu____15400 =
                                      let uu____15407 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15407 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15400 in
                                  if uu____15399
                                  then
                                    let uu____15412 =
                                      let uu____15413 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15413 in
                                    failwith uu____15412
                                  else ());
                                 (let uu____15415 =
                                    maybe_unfold_action head_app in
                                  match uu____15415 with
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
                                      let uu____15454 = FStar_List.tl stack1 in
                                      norm cfg env uu____15454 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15468 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15468 in
                           let uu____15469 = FStar_List.tl stack1 in
                           norm cfg env uu____15469 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15590  ->
                                     match uu____15590 with
                                     | (pat,wopt,tm) ->
                                         let uu____15638 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15638))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15670 = FStar_List.tl stack1 in
                           norm cfg env uu____15670 tm
                       | uu____15671 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15679 = should_reify cfg stack1 in
                    if uu____15679
                    then
                      let uu____15680 = FStar_List.tl stack1 in
                      let uu____15681 =
                        let uu____15682 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15682 in
                      norm cfg env uu____15680 uu____15681
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15685 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15685
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___350_15694 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___350_15694.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___350_15694.primitive_steps);
                             strong = (uu___350_15694.strong)
                           } in
                         norm cfg1 env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack2)
                           head1
                       else
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t3)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack1)
                           head1)
                | uu____15696 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15698::uu____15699 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15704) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15705 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15736 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15750 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15750
                             | uu____15761 -> m in
                           let t2 =
                             mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack1 t2)))
and do_unfold_fv:
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____15773 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15773 in
            let uu____15774 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15774 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15787  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15798  ->
                      let uu____15799 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15800 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15799
                        uu____15800);
                 (let t1 =
                    let uu____15802 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15802
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t in
                  let n1 = FStar_List.length us in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack1 with
                    | (UnivArgs (us',uu____15812))::stack2 ->
                        ((let uu____15821 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug cfg.tcenv)
                              (FStar_Options.Other "univ_norm") in
                          if uu____15821
                          then
                            FStar_List.iter
                              (fun x  ->
                                 let uu____15825 =
                                   FStar_Syntax_Print.univ_to_string x in
                                 FStar_Util.print1 "Univ (normalizer) %s\n"
                                   uu____15825) us'
                          else ());
                         (let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun u  ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env) in
                          norm cfg env1 stack2 t1))
                    | uu____15874 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15877 ->
                        let uu____15880 =
                          let uu____15881 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15881 in
                        failwith uu____15880
                  else norm cfg env stack1 t1))
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
              let uu____15891 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15891 with
              | (uu____15892,return_repr) ->
                  let return_inst =
                    let uu____15901 =
                      let uu____15902 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15902.FStar_Syntax_Syntax.n in
                    match uu____15901 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15908::[]) ->
                        let uu____15915 =
                          let uu____15918 =
                            let uu____15919 =
                              let uu____15926 =
                                let uu____15929 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15929] in
                              (return_tm, uu____15926) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15919 in
                          FStar_Syntax_Syntax.mk uu____15918 in
                        uu____15915 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15937 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15940 =
                    let uu____15943 =
                      let uu____15944 =
                        let uu____15959 =
                          let uu____15962 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15963 =
                            let uu____15966 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15966] in
                          uu____15962 :: uu____15963 in
                        (return_inst, uu____15959) in
                      FStar_Syntax_Syntax.Tm_app uu____15944 in
                    FStar_Syntax_Syntax.mk uu____15943 in
                  uu____15940 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15975 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15975 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15978 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15978
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15979;
                     FStar_TypeChecker_Env.mtarget = uu____15980;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15981;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15992;
                     FStar_TypeChecker_Env.mtarget = uu____15993;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15994;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16012 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16012)
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
                (fun uu____16068  ->
                   match uu____16068 with
                   | (a,imp) ->
                       let uu____16079 = norm cfg env [] a in
                       (uu____16079, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___351_16096 = comp1 in
            let uu____16099 =
              let uu____16100 =
                let uu____16109 = norm cfg env [] t in
                let uu____16110 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16109, uu____16110) in
              FStar_Syntax_Syntax.Total uu____16100 in
            {
              FStar_Syntax_Syntax.n = uu____16099;
              FStar_Syntax_Syntax.pos =
                (uu___351_16096.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___351_16096.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___352_16125 = comp1 in
            let uu____16128 =
              let uu____16129 =
                let uu____16138 = norm cfg env [] t in
                let uu____16139 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16138, uu____16139) in
              FStar_Syntax_Syntax.GTotal uu____16129 in
            {
              FStar_Syntax_Syntax.n = uu____16128;
              FStar_Syntax_Syntax.pos =
                (uu___352_16125.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___352_16125.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16191  ->
                      match uu____16191 with
                      | (a,i) ->
                          let uu____16202 = norm cfg env [] a in
                          (uu____16202, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___301_16213  ->
                      match uu___301_16213 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16217 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16217
                      | f -> f)) in
            let uu___353_16221 = comp1 in
            let uu____16224 =
              let uu____16225 =
                let uu___354_16226 = ct in
                let uu____16227 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16228 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16231 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16227;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___354_16226.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16228;
                  FStar_Syntax_Syntax.effect_args = uu____16231;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16225 in
            {
              FStar_Syntax_Syntax.n = uu____16224;
              FStar_Syntax_Syntax.pos =
                (uu___353_16221.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___353_16221.FStar_Syntax_Syntax.vars)
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
            (let uu___355_16249 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___355_16249.tcenv);
               delta_level = (uu___355_16249.delta_level);
               primitive_steps = (uu___355_16249.primitive_steps);
               strong = (uu___355_16249.strong)
             }) env [] t in
        let non_info t =
          let uu____16254 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16254 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16257 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___356_16276 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___356_16276.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___356_16276.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16283 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16283
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | FStar_Pervasives_Native.Some pure_eff ->
                    let flags =
                      if
                        FStar_Ident.lid_equals pure_eff
                          FStar_Parser_Const.effect_Tot_lid
                      then FStar_Syntax_Syntax.TOTAL ::
                        (ct.FStar_Syntax_Syntax.flags)
                      else ct.FStar_Syntax_Syntax.flags in
                    let uu___357_16294 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___357_16294.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___357_16294.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___357_16294.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___358_16296 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___358_16296.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___358_16296.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___358_16296.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___358_16296.FStar_Syntax_Syntax.flags)
                    } in
              let uu___359_16297 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___359_16297.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___359_16297.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16299 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16302  ->
        match uu____16302 with
        | (x,imp) ->
            let uu____16305 =
              let uu___360_16306 = x in
              let uu____16307 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___360_16306.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___360_16306.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16307
              } in
            (uu____16305, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16313 =
          FStar_List.fold_left
            (fun uu____16331  ->
               fun b  ->
                 match uu____16331 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16313 with | (nbs,uu____16371) -> FStar_List.rev nbs
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
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____16387 =
              let uu___361_16388 = rc in
              let uu____16389 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___361_16388.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16389;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___361_16388.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16387
        | uu____16396 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16409  ->
               let uu____16410 = FStar_Syntax_Print.tag_of_term t in
               let uu____16411 = FStar_Syntax_Print.term_to_string t in
               let uu____16412 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16419 =
                 let uu____16420 =
                   let uu____16423 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16423 in
                 stack_to_string uu____16420 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16410 uu____16411 uu____16412 uu____16419);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16452 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16452
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16454 =
                     let uu____16455 =
                       let uu____16456 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16456 in
                     FStar_Util.string_of_int uu____16455 in
                   let uu____16461 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16462 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16454 uu____16461 uu____16462
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___362_16480 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___362_16480.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___362_16480.strong)
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16521  ->
                     let uu____16522 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16522);
                rebuild cfg env stack2 t)
           | (Let (env',bs,lb,r))::stack2 ->
               let body = FStar_Syntax_Subst.close bs t in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack2 t1
           | (Abs (env',bs,env'',lopt,r))::stack2 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____16558 =
                 let uu___363_16559 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___363_16559.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___363_16559.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16558
           | (Arg (Univ uu____16560,uu____16561,uu____16562))::uu____16563 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16566,uu____16567))::uu____16568 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16584),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16637  ->
                     let uu____16638 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16638);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t1 =
                       FStar_Syntax_Syntax.extend_app t (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack2 t1
                   else
                     (let stack3 = (App (env, t, aq, r)) :: stack2 in
                      norm cfg env_arg stack3 tm))
                else
                  (let uu____16648 = FStar_ST.op_Bang m in
                   match uu____16648 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t1 =
                           FStar_Syntax_Syntax.extend_app t (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack2 t1
                       else
                         (let stack3 = (MemoLazy m) :: (App (env, t, aq, r))
                            :: stack2 in
                          norm cfg env_arg stack3 tm)
                   | FStar_Pervasives_Native.Some (uu____16792,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16835 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16835
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16847  ->
                     let uu____16848 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16848);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16853 =
                   log cfg
                     (fun uu____16858  ->
                        let uu____16859 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16860 =
                          let uu____16861 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16878  ->
                                    match uu____16878 with
                                    | (p,uu____16888,uu____16889) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16861
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16859 uu____16860);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___302_16906  ->
                                match uu___302_16906 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16907 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___364_16911 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___364_16911.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___364_16911.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16943 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16964 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17024  ->
                                    fun uu____17025  ->
                                      match (uu____17024, uu____17025) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17116 = norm_pat env3 p1 in
                                          (match uu____17116 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16964 with
                           | (pats1,env3) ->
                               ((let uu___365_17198 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___365_17198.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___366_17217 = x in
                            let uu____17218 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___366_17217.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___366_17217.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17218
                            } in
                          ((let uu___367_17232 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___367_17232.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___368_17243 = x in
                            let uu____17244 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___368_17243.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___368_17243.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17244
                            } in
                          ((let uu___369_17258 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___369_17258.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___370_17274 = x in
                            let uu____17275 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___370_17274.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___370_17274.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17275
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___371_17282 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___371_17282.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17292 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17306 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17306 with
                                  | (p,wopt,e) ->
                                      let uu____17326 = norm_pat env1 p in
                                      (match uu____17326 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17351 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17351 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17357 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17357) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17367) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17372 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17373;
                         FStar_Syntax_Syntax.fv_delta = uu____17374;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17375;
                         FStar_Syntax_Syntax.fv_delta = uu____17376;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17377);_}
                       -> true
                   | uu____17384 -> false in
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
                   let uu____17529 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17529 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17616 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17655 ->
                                 let uu____17656 =
                                   let uu____17657 = is_cons head1 in
                                   Prims.op_Negation uu____17657 in
                                 FStar_Util.Inr uu____17656)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17682 =
                              let uu____17683 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17683.FStar_Syntax_Syntax.n in
                            (match uu____17682 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17701 ->
                                 let uu____17702 =
                                   let uu____17703 = is_cons head1 in
                                   Prims.op_Negation uu____17703 in
                                 FStar_Util.Inr uu____17702))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17772)::rest_a,(p1,uu____17775)::rest_p) ->
                       let uu____17819 = matches_pat t1 p1 in
                       (match uu____17819 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17868 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17974 = matches_pat scrutinee1 p1 in
                       (match uu____17974 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18014  ->
                                  let uu____18015 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18016 =
                                    let uu____18017 =
                                      FStar_List.map
                                        (fun uu____18027  ->
                                           match uu____18027 with
                                           | (uu____18032,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18017
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18015 uu____18016);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18063  ->
                                       match uu____18063 with
                                       | (bv,t1) ->
                                           let uu____18086 =
                                             let uu____18093 =
                                               let uu____18096 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18096 in
                                             let uu____18097 =
                                               let uu____18098 =
                                                 let uu____18129 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18129, false) in
                                               Clos uu____18098 in
                                             (uu____18093, uu____18097) in
                                           uu____18086 :: env2) env1 s in
                              let uu____18238 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18238))) in
                 let uu____18239 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18239
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___303_18260  ->
                match uu___303_18260 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18264 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18270 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false
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
            let uu___372_18295 = config s e in
            {
              steps = (uu___372_18295.steps);
              tcenv = (uu___372_18295.tcenv);
              delta_level = (uu___372_18295.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___372_18295.strong)
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
      fun t  -> let uu____18320 = config s e in norm_comp uu____18320 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18333 = config [] env in norm_universe uu____18333 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18346 = config [] env in ghost_to_pure_aux uu____18346 [] c
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
        let uu____18364 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18364 in
      let uu____18371 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18371
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___373_18373 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___373_18373.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___373_18373.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18376  ->
                    let uu____18377 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18377))
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
            ((let uu____18394 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18394);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18405 = config [AllowUnboundUniverses] env in
          norm_comp uu____18405 [] c
        with
        | e ->
            ((let uu____18418 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18418);
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
                   let uu____18455 =
                     let uu____18456 =
                       let uu____18463 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18463) in
                     FStar_Syntax_Syntax.Tm_refine uu____18456 in
                   mk uu____18455 t01.FStar_Syntax_Syntax.pos
               | uu____18468 -> t2)
          | uu____18469 -> t2 in
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
        let uu____18509 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18509 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18538 ->
                 let uu____18545 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18545 with
                  | (actuals,uu____18555,uu____18556) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18570 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18570 with
                         | (binders,args) ->
                             let uu____18587 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18587
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
      | uu____18595 ->
          let uu____18596 = FStar_Syntax_Util.head_and_args t in
          (match uu____18596 with
           | (head1,args) ->
               let uu____18633 =
                 let uu____18634 = FStar_Syntax_Subst.compress head1 in
                 uu____18634.FStar_Syntax_Syntax.n in
               (match uu____18633 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18637,thead) ->
                    let uu____18663 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18663 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18705 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___378_18713 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___378_18713.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___378_18713.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___378_18713.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___378_18713.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___378_18713.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___378_18713.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___378_18713.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___378_18713.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___378_18713.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___378_18713.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___378_18713.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___378_18713.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___378_18713.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___378_18713.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___378_18713.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___378_18713.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___378_18713.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___378_18713.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___378_18713.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___378_18713.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___378_18713.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___378_18713.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___378_18713.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___378_18713.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___378_18713.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___378_18713.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___378_18713.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___378_18713.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___378_18713.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___378_18713.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___378_18713.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18705 with
                            | (uu____18714,ty,uu____18716) ->
                                eta_expand_with_type env t ty))
                | uu____18717 ->
                    let uu____18718 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___379_18726 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___379_18726.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___379_18726.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___379_18726.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___379_18726.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___379_18726.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___379_18726.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___379_18726.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___379_18726.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___379_18726.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___379_18726.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___379_18726.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___379_18726.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___379_18726.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___379_18726.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___379_18726.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___379_18726.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___379_18726.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___379_18726.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___379_18726.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___379_18726.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___379_18726.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___379_18726.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___379_18726.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___379_18726.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___379_18726.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___379_18726.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___379_18726.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___379_18726.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___379_18726.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___379_18726.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___379_18726.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18718 with
                     | (uu____18727,ty,uu____18729) ->
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
            | (uu____18803,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18809,FStar_Util.Inl t) ->
                let uu____18815 =
                  let uu____18818 =
                    let uu____18819 =
                      let uu____18832 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18832) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18819 in
                  FStar_Syntax_Syntax.mk uu____18818 in
                uu____18815 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18836 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18836 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18863 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18918 ->
                    let uu____18919 =
                      let uu____18928 =
                        let uu____18929 = FStar_Syntax_Subst.compress t3 in
                        uu____18929.FStar_Syntax_Syntax.n in
                      (uu____18928, tc) in
                    (match uu____18919 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18954) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18991) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19030,FStar_Util.Inl uu____19031) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19054 -> failwith "Impossible") in
              (match uu____18863 with
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
          let uu____19159 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19159 with
          | (univ_names1,binders1,tc) ->
              let uu____19217 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19217)
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
          let uu____19252 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19252 with
          | (univ_names1,binders1,tc) ->
              let uu____19312 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19312)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19345 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19345 with
           | (univ_names1,binders1,typ1) ->
               let uu___380_19373 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___380_19373.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___380_19373.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___380_19373.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___380_19373.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___381_19394 = s in
          let uu____19395 =
            let uu____19396 =
              let uu____19405 = FStar_List.map (elim_uvars env) sigs in
              (uu____19405, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19396 in
          {
            FStar_Syntax_Syntax.sigel = uu____19395;
            FStar_Syntax_Syntax.sigrng =
              (uu___381_19394.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_19394.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_19394.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_19394.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19422 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19422 with
           | (univ_names1,uu____19440,typ1) ->
               let uu___382_19454 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___382_19454.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___382_19454.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___382_19454.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___382_19454.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19460 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19460 with
           | (univ_names1,uu____19478,typ1) ->
               let uu___383_19492 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_19492.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_19492.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_19492.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_19492.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19526 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19526 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19549 =
                            let uu____19550 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19550 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19549 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___384_19553 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___384_19553.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___384_19553.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___385_19554 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___385_19554.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___385_19554.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___385_19554.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___385_19554.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___386_19566 = s in
          let uu____19567 =
            let uu____19568 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19568 in
          {
            FStar_Syntax_Syntax.sigel = uu____19567;
            FStar_Syntax_Syntax.sigrng =
              (uu___386_19566.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___386_19566.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___386_19566.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___386_19566.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19572 = elim_uvars_aux_t env us [] t in
          (match uu____19572 with
           | (us1,uu____19590,t1) ->
               let uu___387_19604 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___387_19604.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___387_19604.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___387_19604.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___387_19604.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19605 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19607 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19607 with
           | (univs1,binders,signature) ->
               let uu____19635 =
                 let uu____19644 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19644 with
                 | (univs_opening,univs2) ->
                     let uu____19671 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19671) in
               (match uu____19635 with
                | (univs_opening,univs_closing) ->
                    let uu____19688 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19694 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19695 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19694, uu____19695) in
                    (match uu____19688 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19717 =
                           match uu____19717 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19735 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19735 with
                                | (us1,t1) ->
                                    let uu____19746 =
                                      let uu____19751 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19758 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19751, uu____19758) in
                                    (match uu____19746 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19771 =
                                           let uu____19776 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19785 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19776, uu____19785) in
                                         (match uu____19771 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19801 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19801 in
                                              let uu____19802 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19802 with
                                               | (uu____19823,uu____19824,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19839 =
                                                       let uu____19840 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19840 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19839 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19845 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19845 with
                           | (uu____19858,uu____19859,t1) -> t1 in
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
                             | uu____19919 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19936 =
                               let uu____19937 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19937.FStar_Syntax_Syntax.n in
                             match uu____19936 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19996 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20025 =
                               let uu____20026 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20026.FStar_Syntax_Syntax.n in
                             match uu____20025 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20047) ->
                                 let uu____20068 = destruct_action_body body in
                                 (match uu____20068 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20113 ->
                                 let uu____20114 = destruct_action_body t in
                                 (match uu____20114 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20163 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20163 with
                           | (action_univs,t) ->
                               let uu____20172 = destruct_action_typ_templ t in
                               (match uu____20172 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___388_20213 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___388_20213.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___388_20213.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___389_20215 = ed in
                           let uu____20216 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20217 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20218 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20219 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20220 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20221 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20222 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20223 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20224 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20225 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20226 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20227 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20228 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20229 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___389_20215.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___389_20215.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20216;
                             FStar_Syntax_Syntax.bind_wp = uu____20217;
                             FStar_Syntax_Syntax.if_then_else = uu____20218;
                             FStar_Syntax_Syntax.ite_wp = uu____20219;
                             FStar_Syntax_Syntax.stronger = uu____20220;
                             FStar_Syntax_Syntax.close_wp = uu____20221;
                             FStar_Syntax_Syntax.assert_p = uu____20222;
                             FStar_Syntax_Syntax.assume_p = uu____20223;
                             FStar_Syntax_Syntax.null_wp = uu____20224;
                             FStar_Syntax_Syntax.trivial = uu____20225;
                             FStar_Syntax_Syntax.repr = uu____20226;
                             FStar_Syntax_Syntax.return_repr = uu____20227;
                             FStar_Syntax_Syntax.bind_repr = uu____20228;
                             FStar_Syntax_Syntax.actions = uu____20229
                           } in
                         let uu___390_20232 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___390_20232.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___390_20232.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___390_20232.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___390_20232.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___304_20249 =
            match uu___304_20249 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20276 = elim_uvars_aux_t env us [] t in
                (match uu____20276 with
                 | (us1,uu____20300,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___391_20319 = sub_eff in
            let uu____20320 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20323 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___391_20319.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___391_20319.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20320;
              FStar_Syntax_Syntax.lift = uu____20323
            } in
          let uu___392_20326 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___392_20326.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___392_20326.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___392_20326.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___392_20326.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20336 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20336 with
           | (univ_names1,binders1,comp1) ->
               let uu___393_20370 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___393_20370.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___393_20370.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___393_20370.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___393_20370.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20381 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t