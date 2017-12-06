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
  fun uu___189_497  ->
    match uu___189_497 with
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
  fun uu___190_1392  ->
    match uu___190_1392 with
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
  fun uu___191_1508  ->
    match uu___191_1508 with | [] -> true | uu____1511 -> false
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
                 let uu____1704 =
                   let uu____1705 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1705 in
                 match uu____1704 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1723 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1732 ->
                   let uu____1733 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1733
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1739 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1748 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1757 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1764 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1764 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1781 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1781 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1789 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1797 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1797 with
                                  | (uu____1802,m) -> n1 <= m)) in
                        if uu____1789 then rest1 else us1
                    | uu____1807 -> us1)
               | uu____1812 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1816 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1816 in
        let uu____1819 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1819
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1821 = aux u in
           match uu____1821 with
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
          (fun uu____1925  ->
             let uu____1926 = FStar_Syntax_Print.tag_of_term t in
             let uu____1927 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1926
               uu____1927);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1934 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1936 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1961 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1962 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1963 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1964 ->
                  let uu____1981 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1981
                  then
                    let uu____1982 =
                      let uu____1983 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1984 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1983 uu____1984 in
                    failwith uu____1982
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1987 =
                    let uu____1988 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1988 in
                  mk uu____1987 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1995 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1995
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1997 = lookup_bvar env x in
                  (match uu____1997 with
                   | Univ uu____2000 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2004) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2116 = closures_as_binders_delayed cfg env bs in
                  (match uu____2116 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2144 =
                         let uu____2145 =
                           let uu____2162 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2162) in
                         FStar_Syntax_Syntax.Tm_abs uu____2145 in
                       mk uu____2144 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2193 = closures_as_binders_delayed cfg env bs in
                  (match uu____2193 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2235 =
                    let uu____2246 =
                      let uu____2253 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2253] in
                    closures_as_binders_delayed cfg env uu____2246 in
                  (match uu____2235 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2271 =
                         let uu____2272 =
                           let uu____2279 =
                             let uu____2280 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2280
                               FStar_Pervasives_Native.fst in
                           (uu____2279, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2272 in
                       mk uu____2271 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2371 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2371
                    | FStar_Util.Inr c ->
                        let uu____2385 = close_comp cfg env c in
                        FStar_Util.Inr uu____2385 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2401 =
                    let uu____2402 =
                      let uu____2429 = closure_as_term_delayed cfg env t11 in
                      (uu____2429, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2402 in
                  mk uu____2401 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2480 =
                    let uu____2481 =
                      let uu____2488 = closure_as_term_delayed cfg env t' in
                      let uu____2491 =
                        let uu____2492 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2492 in
                      (uu____2488, uu____2491) in
                    FStar_Syntax_Syntax.Tm_meta uu____2481 in
                  mk uu____2480 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2552 =
                    let uu____2553 =
                      let uu____2560 = closure_as_term_delayed cfg env t' in
                      let uu____2563 =
                        let uu____2564 =
                          let uu____2571 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2571) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2564 in
                      (uu____2560, uu____2563) in
                    FStar_Syntax_Syntax.Tm_meta uu____2553 in
                  mk uu____2552 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2590 =
                    let uu____2591 =
                      let uu____2598 = closure_as_term_delayed cfg env t' in
                      let uu____2601 =
                        let uu____2602 =
                          let uu____2611 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2611) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2602 in
                      (uu____2598, uu____2601) in
                    FStar_Syntax_Syntax.Tm_meta uu____2591 in
                  mk uu____2590 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2624 =
                    let uu____2625 =
                      let uu____2632 = closure_as_term_delayed cfg env t' in
                      (uu____2632, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2625 in
                  mk uu____2624 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2672  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2691 =
                    let uu____2702 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2702
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2721 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___210_2733 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___210_2733.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___210_2733.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2721)) in
                  (match uu____2691 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___211_2749 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___211_2749.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___211_2749.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2760,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2819  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2844 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2844
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2864  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2886 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2886
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___212_2898 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___212_2898.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___212_2898.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___213_2899 = lb in
                    let uu____2900 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___213_2899.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___213_2899.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2900
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2930  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3019 =
                    match uu____3019 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3074 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3095 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3155  ->
                                        fun uu____3156  ->
                                          match (uu____3155, uu____3156) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3247 =
                                                norm_pat env3 p1 in
                                              (match uu____3247 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3095 with
                               | (pats1,env3) ->
                                   ((let uu___214_3329 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___214_3329.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___215_3348 = x in
                                let uu____3349 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___215_3348.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___215_3348.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3349
                                } in
                              ((let uu___216_3363 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___216_3363.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___217_3374 = x in
                                let uu____3375 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___217_3374.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___217_3374.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3375
                                } in
                              ((let uu___218_3389 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___218_3389.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___219_3405 = x in
                                let uu____3406 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___219_3405.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___219_3405.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3406
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___220_3413 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___220_3413.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3416 = norm_pat env1 pat in
                        (match uu____3416 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3445 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3445 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3451 =
                    let uu____3452 =
                      let uu____3475 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3475) in
                    FStar_Syntax_Syntax.Tm_match uu____3452 in
                  mk uu____3451 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3561 -> closure_as_term cfg env t
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
        | uu____3587 ->
            FStar_List.map
              (fun uu____3604  ->
                 match uu____3604 with
                 | (x,imp) ->
                     let uu____3623 = closure_as_term_delayed cfg env x in
                     (uu____3623, imp)) args
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
        let uu____3637 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3686  ->
                  fun uu____3687  ->
                    match (uu____3686, uu____3687) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___221_3757 = b in
                          let uu____3758 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___221_3757.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___221_3757.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3758
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3637 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3851 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3864 = closure_as_term_delayed cfg env t in
                 let uu____3865 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3864 uu____3865
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3878 = closure_as_term_delayed cfg env t in
                 let uu____3879 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3878 uu____3879
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
                        (fun uu___192_3905  ->
                           match uu___192_3905 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3909 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3909
                           | f -> f)) in
                 let uu____3913 =
                   let uu___222_3914 = c1 in
                   let uu____3915 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3915;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___222_3914.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3913)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___193_3925  ->
            match uu___193_3925 with
            | FStar_Syntax_Syntax.DECREASES uu____3926 -> false
            | uu____3929 -> true))
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
                   (fun uu___194_3947  ->
                      match uu___194_3947 with
                      | FStar_Syntax_Syntax.DECREASES uu____3948 -> false
                      | uu____3951 -> true)) in
            let rc1 =
              let uu___223_3953 = rc in
              let uu____3954 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___223_3953.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3954;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3961 -> lopt
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
    let uu____4051 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4051 in
  let arg_as_bounded_int uu____4079 =
    match uu____4079 with
    | (a,uu____4091) ->
        let uu____4098 =
          let uu____4099 = FStar_Syntax_Subst.compress a in
          uu____4099.FStar_Syntax_Syntax.n in
        (match uu____4098 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4109;
                FStar_Syntax_Syntax.vars = uu____4110;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4112;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4113;_},uu____4114)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4153 =
               let uu____4158 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4158) in
             FStar_Pervasives_Native.Some uu____4153
         | uu____4163 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4205 = f a in FStar_Pervasives_Native.Some uu____4205
    | uu____4206 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4256 = f a0 a1 in FStar_Pervasives_Native.Some uu____4256
    | uu____4257 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4306 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4306 in
  let binary_op as_a f res args =
    let uu____4362 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4362 in
  let as_primitive_step uu____4386 =
    match uu____4386 with
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
           let uu____4434 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4434) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4462 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4462) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4483 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4483) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4511 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4511) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4539 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4539) in
  let list_of_string' rng s =
    let name l =
      let uu____4553 =
        let uu____4554 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4554 in
      mk uu____4553 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4564 =
      let uu____4567 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4567 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4564 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4599 =
      let uu____4600 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4600 in
    FStar_Syntax_Embeddings.embed_int rng uu____4599 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4618 = arg_as_string a1 in
        (match uu____4618 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4624 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4624 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4637 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4637
              | uu____4638 -> FStar_Pervasives_Native.None)
         | uu____4643 -> FStar_Pervasives_Native.None)
    | uu____4646 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4656 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4656 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4680 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4691 =
          let uu____4712 = arg_as_string fn in
          let uu____4715 = arg_as_int from_line in
          let uu____4718 = arg_as_int from_col in
          let uu____4721 = arg_as_int to_line in
          let uu____4724 = arg_as_int to_col in
          (uu____4712, uu____4715, uu____4718, uu____4721, uu____4724) in
        (match uu____4691 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4755 =
                 let uu____4756 = FStar_BigInt.to_int_fs from_l in
                 let uu____4757 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4756 uu____4757 in
               let uu____4758 =
                 let uu____4759 = FStar_BigInt.to_int_fs to_l in
                 let uu____4760 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4759 uu____4760 in
               FStar_Range.mk_range fn1 uu____4755 uu____4758 in
             let uu____4761 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4761
         | uu____4766 -> FStar_Pervasives_Native.None)
    | uu____4787 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4814)::(a1,uu____4816)::(a2,uu____4818)::[] ->
        let uu____4855 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4855 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4868 -> FStar_Pervasives_Native.None)
    | uu____4869 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4896)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4905 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____4929 =
      let uu____4944 =
        let uu____4959 =
          let uu____4974 =
            let uu____4989 =
              let uu____5004 =
                let uu____5019 =
                  let uu____5034 =
                    let uu____5049 =
                      let uu____5064 =
                        let uu____5079 =
                          let uu____5094 =
                            let uu____5109 =
                              let uu____5124 =
                                let uu____5139 =
                                  let uu____5154 =
                                    let uu____5169 =
                                      let uu____5184 =
                                        let uu____5199 =
                                          let uu____5214 =
                                            let uu____5227 =
                                              FStar_Parser_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____5227,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____5234 =
                                            let uu____5249 =
                                              let uu____5262 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____5262,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list
                                                      FStar_Syntax_Embeddings.unembed_char_safe)
                                                   string_of_list')) in
                                            let uu____5273 =
                                              let uu____5288 =
                                                let uu____5303 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____5303,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              let uu____5312 =
                                                let uu____5329 =
                                                  let uu____5344 =
                                                    FStar_Parser_Const.p2l
                                                      ["Prims"; "mk_range"] in
                                                  (uu____5344,
                                                    (Prims.parse_int "5"),
                                                    mk_range1) in
                                                let uu____5353 =
                                                  let uu____5370 =
                                                    let uu____5389 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "Range";
                                                        "prims_to_fstar_range"] in
                                                    (uu____5389,
                                                      (Prims.parse_int "1"),
                                                      idstep) in
                                                  [uu____5370] in
                                                uu____5329 :: uu____5353 in
                                              uu____5288 :: uu____5312 in
                                            uu____5249 :: uu____5273 in
                                          uu____5214 :: uu____5234 in
                                        (FStar_Parser_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____5199 in
                                      (FStar_Parser_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____5184 in
                                    (FStar_Parser_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____5169 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____5154 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____5139 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5124 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5109 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5094 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5079 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5064 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5725 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5725)))
                      :: uu____5049 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5751 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5751)))
                    :: uu____5034 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5777 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5777)))
                  :: uu____5019 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5803 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5803)))
                :: uu____5004 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____4989 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____4974 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____4959 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____4944 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____4929 in
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
      let uu____5953 =
        let uu____5954 =
          let uu____5955 = FStar_Syntax_Syntax.as_arg c in [uu____5955] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5954 in
      uu____5953 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____5990 =
              let uu____6003 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6003, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6023  ->
                        fun uu____6024  ->
                          match (uu____6023, uu____6024) with
                          | ((int_to_t1,x),(uu____6043,y)) ->
                              let uu____6053 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6053))) in
            let uu____6054 =
              let uu____6069 =
                let uu____6082 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6082, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6102  ->
                          fun uu____6103  ->
                            match (uu____6102, uu____6103) with
                            | ((int_to_t1,x),(uu____6122,y)) ->
                                let uu____6132 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6132))) in
              let uu____6133 =
                let uu____6148 =
                  let uu____6161 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6161, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6181  ->
                            fun uu____6182  ->
                              match (uu____6181, uu____6182) with
                              | ((int_to_t1,x),(uu____6201,y)) ->
                                  let uu____6211 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6211))) in
                [uu____6148] in
              uu____6069 :: uu____6133 in
            uu____5990 :: uu____6054)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6301)::(a1,uu____6303)::(a2,uu____6305)::[] ->
        let uu____6342 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6342 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6348 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6348.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6348.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___225_6352 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___225_6352.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___225_6352.FStar_Syntax_Syntax.vars)
                })
         | uu____6353 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6355)::uu____6356::(a1,uu____6358)::(a2,uu____6360)::[] ->
        let uu____6409 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6409 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6415 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6415.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6415.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___225_6419 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___225_6419.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___225_6419.FStar_Syntax_Syntax.vars)
                })
         | uu____6420 -> FStar_Pervasives_Native.None)
    | uu____6421 -> failwith "Unexpected number of arguments" in
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
      let uu____6440 =
        let uu____6441 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6441 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6440
    with | uu____6447 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6451 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6451) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6511  ->
           fun subst1  ->
             match uu____6511 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6553)) ->
                      let uu____6612 = b in
                      (match uu____6612 with
                       | (bv,uu____6620) ->
                           let uu____6621 =
                             let uu____6622 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6622 in
                           if uu____6621
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6627 = unembed_binder term1 in
                              match uu____6627 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6634 =
                                      let uu___228_6635 = bv in
                                      let uu____6636 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___228_6635.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___228_6635.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6636
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6634 in
                                  let b_for_x =
                                    let uu____6640 =
                                      let uu____6647 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6647) in
                                    FStar_Syntax_Syntax.NT uu____6640 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___195_6656  ->
                                         match uu___195_6656 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6657,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6659;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6660;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6665 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6666 -> subst1)) env []
let reduce_primops:
  'Auu____6683 'Auu____6684 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6684) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6683 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6725 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6725
          then tm
          else
            (let uu____6727 = FStar_Syntax_Util.head_and_args tm in
             match uu____6727 with
             | (head1,args) ->
                 let uu____6764 =
                   let uu____6765 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6765.FStar_Syntax_Syntax.n in
                 (match uu____6764 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6769 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6769 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6786  ->
                                   let uu____6787 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6788 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6795 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6787 uu____6788 uu____6795);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6800  ->
                                   let uu____6801 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6801);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6804  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6806 =
                                 prim_step.interpretation psc args in
                               match uu____6806 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6812  ->
                                         let uu____6813 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6813);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6819  ->
                                         let uu____6820 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6821 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6820 uu____6821);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6822 ->
                           (log_primops cfg
                              (fun uu____6826  ->
                                 let uu____6827 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6827);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6831  ->
                            let uu____6832 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6832);
                       (match args with
                        | (a1,uu____6834)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6851 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6863  ->
                            let uu____6864 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6864);
                       (match args with
                        | (a1,uu____6866)::(a2,uu____6868)::[] ->
                            let uu____6895 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____6895 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___229_6899 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___229_6899.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___229_6899.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6902 -> tm))
                  | uu____6911 -> tm))
let reduce_equality:
  'Auu____6916 'Auu____6917 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6917) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6916 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___230_6955 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___230_6955.tcenv);
           delta_level = (uu___230_6955.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___230_6955.strong)
         }) tm
let maybe_simplify:
  'Auu____6962 'Auu____6963 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6963) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6962 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7005 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7005
          then tm1
          else
            (let w t =
               let uu___231_7017 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___231_7017.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___231_7017.FStar_Syntax_Syntax.vars)
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
               | uu____7034 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7074;
                         FStar_Syntax_Syntax.vars = uu____7075;_},uu____7076);
                    FStar_Syntax_Syntax.pos = uu____7077;
                    FStar_Syntax_Syntax.vars = uu____7078;_},args)
                 ->
                 let uu____7104 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7104
                 then
                   let uu____7105 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7105 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7160)::
                        (uu____7161,(arg,uu____7163))::[] -> arg
                    | (uu____7228,(arg,uu____7230))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7231)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7296)::uu____7297::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7360::(FStar_Pervasives_Native.Some (false
                                   ),uu____7361)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7424 -> tm1)
                 else
                   (let uu____7440 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7440
                    then
                      let uu____7441 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7441 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7496)::uu____7497::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7560::(FStar_Pervasives_Native.Some (true
                                     ),uu____7561)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7624)::
                          (uu____7625,(arg,uu____7627))::[] -> arg
                      | (uu____7692,(arg,uu____7694))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7695)::[]
                          -> arg
                      | uu____7760 -> tm1
                    else
                      (let uu____7776 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7776
                       then
                         let uu____7777 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7777 with
                         | uu____7832::(FStar_Pervasives_Native.Some (true
                                        ),uu____7833)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____7896)::uu____7897::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____7960)::
                             (uu____7961,(arg,uu____7963))::[] -> arg
                         | (uu____8028,(p,uu____8030))::(uu____8031,(q,uu____8033))::[]
                             ->
                             let uu____8098 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8098
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8100 -> tm1
                       else
                         (let uu____8116 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8116
                          then
                            let uu____8117 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8117 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8172)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8211)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8250 -> tm1
                          else
                            (let uu____8266 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8266
                             then
                               match args with
                               | (t,uu____8268)::[] ->
                                   let uu____8285 =
                                     let uu____8286 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8286.FStar_Syntax_Syntax.n in
                                   (match uu____8285 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8289::[],body,uu____8291) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8318 -> tm1)
                                    | uu____8321 -> tm1)
                               | (uu____8322,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8323))::
                                   (t,uu____8325)::[] ->
                                   let uu____8364 =
                                     let uu____8365 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8365.FStar_Syntax_Syntax.n in
                                   (match uu____8364 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8368::[],body,uu____8370) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8397 -> tm1)
                                    | uu____8400 -> tm1)
                               | uu____8401 -> tm1
                             else
                               (let uu____8411 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8411
                                then
                                  match args with
                                  | (t,uu____8413)::[] ->
                                      let uu____8430 =
                                        let uu____8431 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8431.FStar_Syntax_Syntax.n in
                                      (match uu____8430 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8434::[],body,uu____8436)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8463 -> tm1)
                                       | uu____8466 -> tm1)
                                  | (uu____8467,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8468))::(t,uu____8470)::[] ->
                                      let uu____8509 =
                                        let uu____8510 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8510.FStar_Syntax_Syntax.n in
                                      (match uu____8509 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8513::[],body,uu____8515)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8542 -> tm1)
                                       | uu____8545 -> tm1)
                                  | uu____8546 -> tm1
                                else
                                  (let uu____8556 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8556
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8557;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8558;_},uu____8559)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8576;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8577;_},uu____8578)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8595 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8606;
                    FStar_Syntax_Syntax.vars = uu____8607;_},args)
                 ->
                 let uu____8629 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8629
                 then
                   let uu____8630 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8630 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8685)::
                        (uu____8686,(arg,uu____8688))::[] -> arg
                    | (uu____8753,(arg,uu____8755))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8756)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8821)::uu____8822::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8885::(FStar_Pervasives_Native.Some (false
                                   ),uu____8886)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8949 -> tm1)
                 else
                   (let uu____8965 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8965
                    then
                      let uu____8966 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8966 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9021)::uu____9022::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9085::(FStar_Pervasives_Native.Some (true
                                     ),uu____9086)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9149)::
                          (uu____9150,(arg,uu____9152))::[] -> arg
                      | (uu____9217,(arg,uu____9219))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9220)::[]
                          -> arg
                      | uu____9285 -> tm1
                    else
                      (let uu____9301 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9301
                       then
                         let uu____9302 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9302 with
                         | uu____9357::(FStar_Pervasives_Native.Some (true
                                        ),uu____9358)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9421)::uu____9422::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9485)::
                             (uu____9486,(arg,uu____9488))::[] -> arg
                         | (uu____9553,(p,uu____9555))::(uu____9556,(q,uu____9558))::[]
                             ->
                             let uu____9623 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9623
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9625 -> tm1
                       else
                         (let uu____9641 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9641
                          then
                            let uu____9642 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9642 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9697)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9736)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9775 -> tm1
                          else
                            (let uu____9791 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9791
                             then
                               match args with
                               | (t,uu____9793)::[] ->
                                   let uu____9810 =
                                     let uu____9811 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9811.FStar_Syntax_Syntax.n in
                                   (match uu____9810 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9814::[],body,uu____9816) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9843 -> tm1)
                                    | uu____9846 -> tm1)
                               | (uu____9847,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9848))::
                                   (t,uu____9850)::[] ->
                                   let uu____9889 =
                                     let uu____9890 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9890.FStar_Syntax_Syntax.n in
                                   (match uu____9889 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9893::[],body,uu____9895) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9922 -> tm1)
                                    | uu____9925 -> tm1)
                               | uu____9926 -> tm1
                             else
                               (let uu____9936 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9936
                                then
                                  match args with
                                  | (t,uu____9938)::[] ->
                                      let uu____9955 =
                                        let uu____9956 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9956.FStar_Syntax_Syntax.n in
                                      (match uu____9955 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9959::[],body,uu____9961)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9988 -> tm1)
                                       | uu____9991 -> tm1)
                                  | (uu____9992,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9993))::(t,uu____9995)::[] ->
                                      let uu____10034 =
                                        let uu____10035 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10035.FStar_Syntax_Syntax.n in
                                      (match uu____10034 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10038::[],body,uu____10040)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10067 -> tm1)
                                       | uu____10070 -> tm1)
                                  | uu____10071 -> tm1
                                else
                                  (let uu____10081 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10081
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10082;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10083;_},uu____10084)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10101;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10102;_},uu____10103)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10120 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | uu____10130 -> tm1)
let is_norm_request:
  'Auu____10134 .
    FStar_Syntax_Syntax.term -> 'Auu____10134 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10147 =
        let uu____10154 =
          let uu____10155 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10155.FStar_Syntax_Syntax.n in
        (uu____10154, args) in
      match uu____10147 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10161::uu____10162::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10166::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10171::uu____10172::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10175 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___196_10186  ->
    match uu___196_10186 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10192 =
          let uu____10195 =
            let uu____10196 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10196 in
          [uu____10195] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10192
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10211 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10211) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10249 =
          let uu____10252 =
            let uu____10257 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10257 s in
          FStar_All.pipe_right uu____10252 FStar_Util.must in
        FStar_All.pipe_right uu____10249 tr_norm_steps in
      match args with
      | uu____10282::(tm,uu____10284)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10307)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10322)::uu____10323::(tm,uu____10325)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10365 =
              let uu____10368 = full_norm steps in parse_steps uu____10368 in
            Beta :: uu____10365 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10377 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___197_10394  ->
    match uu___197_10394 with
    | (App
        (uu____10397,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10398;
                       FStar_Syntax_Syntax.vars = uu____10399;_},uu____10400,uu____10401))::uu____10402
        -> true
    | uu____10409 -> false
let firstn:
  'Auu____10415 .
    Prims.int ->
      'Auu____10415 Prims.list ->
        ('Auu____10415 Prims.list,'Auu____10415 Prims.list)
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
          (uu____10451,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10452;
                         FStar_Syntax_Syntax.vars = uu____10453;_},uu____10454,uu____10455))::uu____10456
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10463 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10579  ->
               let uu____10580 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10581 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10582 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10589 =
                 let uu____10590 =
                   let uu____10593 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10593 in
                 stack_to_string uu____10590 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10580 uu____10581 uu____10582 uu____10589);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10616 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10641 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10658 =
                 let uu____10659 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10660 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10659 uu____10660 in
               failwith uu____10658
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10661 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10678 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10679 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10680;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10681;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10684;
                 FStar_Syntax_Syntax.fv_delta = uu____10685;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10686;
                 FStar_Syntax_Syntax.fv_delta = uu____10687;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10688);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10696 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10696 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____10702  ->
                     let uu____10703 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10704 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10703 uu____10704);
                if b
                then
                  (let uu____10705 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____10705 t1 fv)
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
                 let uu___232_10744 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___232_10744.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___232_10744.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10777 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10777) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___233_10785 = cfg in
                 let uu____10786 =
                   FStar_List.filter
                     (fun uu___198_10789  ->
                        match uu___198_10789 with
                        | UnfoldOnly uu____10790 -> false
                        | NoDeltaSteps  -> false
                        | uu____10793 -> true) cfg.steps in
                 {
                   steps = uu____10786;
                   tcenv = (uu___233_10785.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___233_10785.primitive_steps);
                   strong = (uu___233_10785.strong)
                 } in
               let uu____10794 = get_norm_request (norm cfg' env []) args in
               (match uu____10794 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10810 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___199_10815  ->
                                match uu___199_10815 with
                                | UnfoldUntil uu____10816 -> true
                                | UnfoldOnly uu____10817 -> true
                                | uu____10820 -> false)) in
                      if uu____10810
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___234_10825 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___234_10825.tcenv);
                        delta_level;
                        primitive_steps = (uu___234_10825.primitive_steps);
                        strong = (uu___234_10825.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____10836 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10836
                      then
                        let uu____10839 =
                          let uu____10840 =
                            let uu____10845 = FStar_Util.now () in
                            (t1, uu____10845) in
                          Debug uu____10840 in
                        uu____10839 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____10847;
                  FStar_Syntax_Syntax.vars = uu____10848;_},a1::a2::rest)
               ->
               let uu____10896 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10896 with
                | (hd1,uu____10912) ->
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
                  FStar_Syntax_Syntax.pos = uu____10977;
                  FStar_Syntax_Syntax.vars = uu____10978;_},a1::a2::rest)
               ->
               let uu____11026 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11026 with
                | (hd1,uu____11042) ->
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
                  FStar_Syntax_Syntax.pos = uu____11107;
                  FStar_Syntax_Syntax.vars = uu____11108;_},a1::a2::a3::rest)
               ->
               let uu____11169 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11169 with
                | (hd1,uu____11185) ->
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
                    (FStar_Const.Const_reflect uu____11256);
                  FStar_Syntax_Syntax.pos = uu____11257;
                  FStar_Syntax_Syntax.vars = uu____11258;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11290 = FStar_List.tl stack in
               norm cfg env uu____11290 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11293;
                  FStar_Syntax_Syntax.vars = uu____11294;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11326 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11326 with
                | (reify_head,uu____11342) ->
                    let a1 =
                      let uu____11364 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11364 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11367);
                            FStar_Syntax_Syntax.pos = uu____11368;
                            FStar_Syntax_Syntax.vars = uu____11369;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11403 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11413 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11413
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11420 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11420
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11423 =
                      let uu____11430 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11430, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11423 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___200_11443  ->
                         match uu___200_11443 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11446 =
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
                 if uu____11446
                 then false
                 else
                   (let uu____11448 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___201_11455  ->
                              match uu___201_11455 with
                              | UnfoldOnly uu____11456 -> true
                              | uu____11459 -> false)) in
                    match uu____11448 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11463 -> should_delta) in
               (log cfg
                  (fun uu____11471  ->
                     let uu____11472 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11473 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11474 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11472 uu____11473 uu____11474);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11477 = lookup_bvar env x in
               (match uu____11477 with
                | Univ uu____11480 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11529 = FStar_ST.op_Bang r in
                      (match uu____11529 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11666  ->
                                 let uu____11667 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11668 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11667
                                   uu____11668);
                            (let uu____11669 =
                               let uu____11670 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11670.FStar_Syntax_Syntax.n in
                             match uu____11669 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11673 ->
                                 norm cfg env2 stack t'
                             | uu____11690 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11748)::uu____11749 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11758)::uu____11759 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11769,uu____11770))::stack_rest ->
                    (match c with
                     | Univ uu____11774 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11783 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11804  ->
                                    let uu____11805 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11805);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11845  ->
                                    let uu____11846 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11846);
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
                      (let uu___235_11896 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___235_11896.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___235_11896.strong)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11929  ->
                          let uu____11930 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11930);
                     norm cfg env stack1 t1)
                | (Debug uu____11931)::uu____11932 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11939 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11939
                    else
                      (let uu____11941 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11941 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11983  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12011 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12011
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12021 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12021)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___236_12026 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___236_12026.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___236_12026.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12027 -> lopt in
                           (log cfg
                              (fun uu____12033  ->
                                 let uu____12034 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12034);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___237_12047 = cfg in
                               {
                                 steps = (uu___237_12047.steps);
                                 tcenv = (uu___237_12047.tcenv);
                                 delta_level = (uu___237_12047.delta_level);
                                 primitive_steps =
                                   (uu___237_12047.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12058)::uu____12059 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12066 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12066
                    else
                      (let uu____12068 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12068 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12110  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12138 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12138
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12148 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12148)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___236_12153 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___236_12153.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___236_12153.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12154 -> lopt in
                           (log cfg
                              (fun uu____12160  ->
                                 let uu____12161 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12161);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___237_12174 = cfg in
                               {
                                 steps = (uu___237_12174.steps);
                                 tcenv = (uu___237_12174.tcenv);
                                 delta_level = (uu___237_12174.delta_level);
                                 primitive_steps =
                                   (uu___237_12174.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12185)::uu____12186 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12197 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12197
                    else
                      (let uu____12199 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12199 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12241  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12269 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12269
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12279 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12279)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___236_12284 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___236_12284.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___236_12284.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12285 -> lopt in
                           (log cfg
                              (fun uu____12291  ->
                                 let uu____12292 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12292);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___237_12305 = cfg in
                               {
                                 steps = (uu___237_12305.steps);
                                 tcenv = (uu___237_12305.tcenv);
                                 delta_level = (uu___237_12305.delta_level);
                                 primitive_steps =
                                   (uu___237_12305.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12316)::uu____12317 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12328 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12328
                    else
                      (let uu____12330 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12330 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12372  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12400 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12400
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12410 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12410)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___236_12415 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___236_12415.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___236_12415.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12416 -> lopt in
                           (log cfg
                              (fun uu____12422  ->
                                 let uu____12423 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12423);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___237_12436 = cfg in
                               {
                                 steps = (uu___237_12436.steps);
                                 tcenv = (uu___237_12436.tcenv);
                                 delta_level = (uu___237_12436.delta_level);
                                 primitive_steps =
                                   (uu___237_12436.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12447)::uu____12448 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12463 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12463
                    else
                      (let uu____12465 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12465 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12507  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12535 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12535
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12545 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12545)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___236_12550 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___236_12550.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___236_12550.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12551 -> lopt in
                           (log cfg
                              (fun uu____12557  ->
                                 let uu____12558 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12558);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___237_12571 = cfg in
                               {
                                 steps = (uu___237_12571.steps);
                                 tcenv = (uu___237_12571.tcenv);
                                 delta_level = (uu___237_12571.delta_level);
                                 primitive_steps =
                                   (uu___237_12571.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12582 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12582
                    else
                      (let uu____12584 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12584 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12626  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12654 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12654
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12664 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12664)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___236_12669 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___236_12669.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___236_12669.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12670 -> lopt in
                           (log cfg
                              (fun uu____12676  ->
                                 let uu____12677 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12677);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___237_12690 = cfg in
                               {
                                 steps = (uu___237_12690.steps);
                                 tcenv = (uu___237_12690.tcenv);
                                 delta_level = (uu___237_12690.delta_level);
                                 primitive_steps =
                                   (uu___237_12690.primitive_steps);
                                 strong = true
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
                      (fun uu____12739  ->
                         fun stack1  ->
                           match uu____12739 with
                           | (a,aq) ->
                               let uu____12751 =
                                 let uu____12752 =
                                   let uu____12759 =
                                     let uu____12760 =
                                       let uu____12791 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12791, false) in
                                     Clos uu____12760 in
                                   (uu____12759, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12752 in
                               uu____12751 :: stack1) args) in
               (log cfg
                  (fun uu____12867  ->
                     let uu____12868 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12868);
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
                             ((let uu___238_12904 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___238_12904.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___238_12904.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12905 ->
                      let uu____12910 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12910)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12913 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12913 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12944 =
                          let uu____12945 =
                            let uu____12952 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___239_12954 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___239_12954.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___239_12954.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12952) in
                          FStar_Syntax_Syntax.Tm_refine uu____12945 in
                        mk uu____12944 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12973 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12973
               else
                 (let uu____12975 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12975 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12983 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13007  -> dummy :: env1) env) in
                        norm_comp cfg uu____12983 c1 in
                      let t2 =
                        let uu____13029 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13029 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13088)::uu____13089 ->
                    (log cfg
                       (fun uu____13100  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13101)::uu____13102 ->
                    (log cfg
                       (fun uu____13113  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13114,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13115;
                                   FStar_Syntax_Syntax.vars = uu____13116;_},uu____13117,uu____13118))::uu____13119
                    ->
                    (log cfg
                       (fun uu____13128  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13129)::uu____13130 ->
                    (log cfg
                       (fun uu____13141  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13142 ->
                    (log cfg
                       (fun uu____13145  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13149  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13166 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13166
                         | FStar_Util.Inr c ->
                             let uu____13174 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13174 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13180 =
                         let uu____13181 =
                           let uu____13182 =
                             let uu____13209 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13209, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13182 in
                         mk uu____13181 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack uu____13180))))
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
                         let uu____13319 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13319 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___240_13339 = cfg in
                               let uu____13340 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___240_13339.steps);
                                 tcenv = uu____13340;
                                 delta_level = (uu___240_13339.delta_level);
                                 primitive_steps =
                                   (uu___240_13339.primitive_steps);
                                 strong = (uu___240_13339.strong)
                               } in
                             let norm1 t2 =
                               let uu____13345 =
                                 let uu____13346 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13346 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13345 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___241_13349 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___241_13349.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___241_13349.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13350 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13350
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13361,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13362;
                               FStar_Syntax_Syntax.lbunivs = uu____13363;
                               FStar_Syntax_Syntax.lbtyp = uu____13364;
                               FStar_Syntax_Syntax.lbeff = uu____13365;
                               FStar_Syntax_Syntax.lbdef = uu____13366;_}::uu____13367),uu____13368)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13404 =
                 (let uu____13407 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13407) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13409 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13409))) in
               if uu____13404
               then
                 let binder =
                   let uu____13411 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13411 in
                 let env1 =
                   let uu____13421 =
                     let uu____13428 =
                       let uu____13429 =
                         let uu____13460 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13460,
                           false) in
                       Clos uu____13429 in
                     ((FStar_Pervasives_Native.Some binder), uu____13428) in
                   uu____13421 :: env in
                 (log cfg
                    (fun uu____13545  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13547 =
                    let uu____13552 =
                      let uu____13553 =
                        let uu____13554 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13554
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13553] in
                    FStar_Syntax_Subst.open_term uu____13552 body in
                  match uu____13547 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13563  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13571 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13571 in
                          FStar_Util.Inl
                            (let uu___242_13581 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___242_13581.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___242_13581.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13584  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___243_13586 = lb in
                           let uu____13587 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___243_13586.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___243_13586.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13587
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13622  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___244_13642 = cfg in
                           {
                             steps = (uu___244_13642.steps);
                             tcenv = (uu___244_13642.tcenv);
                             delta_level = (uu___244_13642.delta_level);
                             primitive_steps =
                               (uu___244_13642.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13645  ->
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
               let uu____13662 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13662 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13698 =
                               let uu___245_13699 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___245_13699.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___245_13699.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13698 in
                           let uu____13700 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13700 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13726 =
                                   FStar_List.map (fun uu____13742  -> dummy)
                                     lbs1 in
                                 let uu____13743 =
                                   let uu____13752 =
                                     FStar_List.map
                                       (fun uu____13772  -> dummy) xs1 in
                                   FStar_List.append uu____13752 env in
                                 FStar_List.append uu____13726 uu____13743 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13796 =
                                       let uu___246_13797 = rc in
                                       let uu____13798 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___246_13797.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13798;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___246_13797.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13796
                                 | uu____13805 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___247_13809 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___247_13809.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___247_13809.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13819 =
                        FStar_List.map (fun uu____13835  -> dummy) lbs2 in
                      FStar_List.append uu____13819 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13843 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13843 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___248_13859 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___248_13859.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___248_13859.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13886 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13886
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13905 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13981  ->
                        match uu____13981 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___249_14102 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___249_14102.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___249_14102.FStar_Syntax_Syntax.sort)
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
               (match uu____13905 with
                | (rec_env,memos,uu____14299) ->
                    let uu____14352 =
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
                             let uu____14883 =
                               let uu____14890 =
                                 let uu____14891 =
                                   let uu____14922 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14922, false) in
                                 Clos uu____14891 in
                               (FStar_Pervasives_Native.None, uu____14890) in
                             uu____14883 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15027 =
                      let uu____15028 = should_reify cfg stack in
                      Prims.op_Negation uu____15028 in
                    if uu____15027
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____15038 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15038
                        then
                          let uu___250_15039 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___250_15039.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___250_15039.primitive_steps);
                            strong = (uu___250_15039.strong)
                          }
                        else
                          (let uu___251_15041 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___251_15041.tcenv);
                             delta_level = (uu___251_15041.delta_level);
                             primitive_steps =
                               (uu___251_15041.primitive_steps);
                             strong = (uu___251_15041.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15043 =
                         let uu____15044 = FStar_Syntax_Subst.compress head1 in
                         uu____15044.FStar_Syntax_Syntax.n in
                       match uu____15043 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15062 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15062 with
                            | (uu____15063,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15069 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15077 =
                                         let uu____15078 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15078.FStar_Syntax_Syntax.n in
                                       match uu____15077 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15084,uu____15085))
                                           ->
                                           let uu____15094 =
                                             let uu____15095 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15095.FStar_Syntax_Syntax.n in
                                           (match uu____15094 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15101,msrc,uu____15103))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15112 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15112
                                            | uu____15113 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15114 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15115 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15115 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___252_15120 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___252_15120.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___252_15120.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___252_15120.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15121 =
                                            FStar_List.tl stack in
                                          let uu____15122 =
                                            let uu____15123 =
                                              let uu____15126 =
                                                let uu____15127 =
                                                  let uu____15140 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15140) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15127 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15126 in
                                            uu____15123
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15121
                                            uu____15122
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15156 =
                                            let uu____15157 = is_return body in
                                            match uu____15157 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15161;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15162;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15167 -> false in
                                          if uu____15156
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
                                               let uu____15191 =
                                                 let uu____15194 =
                                                   let uu____15195 =
                                                     let uu____15212 =
                                                       let uu____15215 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15215] in
                                                     (uu____15212, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15195 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15194 in
                                               uu____15191
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15231 =
                                                 let uu____15232 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15232.FStar_Syntax_Syntax.n in
                                               match uu____15231 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15238::uu____15239::[])
                                                   ->
                                                   let uu____15246 =
                                                     let uu____15249 =
                                                       let uu____15250 =
                                                         let uu____15257 =
                                                           let uu____15260 =
                                                             let uu____15261
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15261 in
                                                           let uu____15262 =
                                                             let uu____15265
                                                               =
                                                               let uu____15266
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15266 in
                                                             [uu____15265] in
                                                           uu____15260 ::
                                                             uu____15262 in
                                                         (bind1, uu____15257) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15250 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15249 in
                                                   uu____15246
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15274 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15280 =
                                                 let uu____15283 =
                                                   let uu____15284 =
                                                     let uu____15299 =
                                                       let uu____15302 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15303 =
                                                         let uu____15306 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15307 =
                                                           let uu____15310 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15311 =
                                                             let uu____15314
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15315
                                                               =
                                                               let uu____15318
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15319
                                                                 =
                                                                 let uu____15322
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15322] in
                                                               uu____15318 ::
                                                                 uu____15319 in
                                                             uu____15314 ::
                                                               uu____15315 in
                                                           uu____15310 ::
                                                             uu____15311 in
                                                         uu____15306 ::
                                                           uu____15307 in
                                                       uu____15302 ::
                                                         uu____15303 in
                                                     (bind_inst, uu____15299) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15284 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15283 in
                                               uu____15280
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15330 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____15330 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15354 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15354 with
                            | (uu____15355,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15390 =
                                        let uu____15391 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15391.FStar_Syntax_Syntax.n in
                                      match uu____15390 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15397) -> t4
                                      | uu____15402 -> head2 in
                                    let uu____15403 =
                                      let uu____15404 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15404.FStar_Syntax_Syntax.n in
                                    match uu____15403 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15410 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15411 = maybe_extract_fv head2 in
                                  match uu____15411 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15421 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15421
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15426 =
                                          maybe_extract_fv head3 in
                                        match uu____15426 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15431 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15432 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15437 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15452 =
                                    match uu____15452 with
                                    | (e,q) ->
                                        let uu____15459 =
                                          let uu____15460 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15460.FStar_Syntax_Syntax.n in
                                        (match uu____15459 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15475 -> false) in
                                  let uu____15476 =
                                    let uu____15477 =
                                      let uu____15484 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15484 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15477 in
                                  if uu____15476
                                  then
                                    let uu____15489 =
                                      let uu____15490 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15490 in
                                    failwith uu____15489
                                  else ());
                                 (let uu____15492 =
                                    maybe_unfold_action head_app in
                                  match uu____15492 with
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
                                      let uu____15531 = FStar_List.tl stack in
                                      norm cfg env uu____15531 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15545 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15545 in
                           let uu____15546 = FStar_List.tl stack in
                           norm cfg env uu____15546 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15667  ->
                                     match uu____15667 with
                                     | (pat,wopt,tm) ->
                                         let uu____15715 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15715))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15747 = FStar_List.tl stack in
                           norm cfg env uu____15747 tm
                       | uu____15748 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15756 = should_reify cfg stack in
                    if uu____15756
                    then
                      let uu____15757 = FStar_List.tl stack in
                      let uu____15758 =
                        let uu____15759 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15759 in
                      norm cfg env uu____15757 uu____15758
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15762 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15762
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___253_15771 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___253_15771.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___253_15771.primitive_steps);
                             strong = (uu___253_15771.strong)
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
                | uu____15773 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____15775::uu____15776 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15781) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15782 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____15813 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15827 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15827
                             | uu____15838 -> m in
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
              let uu____15850 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15850 in
            let uu____15851 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15851 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15864  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15875  ->
                      let uu____15876 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15877 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15876
                        uu____15877);
                 (let t1 =
                    let uu____15879 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15879
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
                    | (UnivArgs (us',uu____15889))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15944 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15947 ->
                        let uu____15950 =
                          let uu____15951 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15951 in
                        failwith uu____15950
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
              let uu____15961 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15961 with
              | (uu____15962,return_repr) ->
                  let return_inst =
                    let uu____15971 =
                      let uu____15972 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15972.FStar_Syntax_Syntax.n in
                    match uu____15971 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15978::[]) ->
                        let uu____15985 =
                          let uu____15988 =
                            let uu____15989 =
                              let uu____15996 =
                                let uu____15999 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15999] in
                              (return_tm, uu____15996) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15989 in
                          FStar_Syntax_Syntax.mk uu____15988 in
                        uu____15985 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16007 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16010 =
                    let uu____16013 =
                      let uu____16014 =
                        let uu____16029 =
                          let uu____16032 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16033 =
                            let uu____16036 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16036] in
                          uu____16032 :: uu____16033 in
                        (return_inst, uu____16029) in
                      FStar_Syntax_Syntax.Tm_app uu____16014 in
                    FStar_Syntax_Syntax.mk uu____16013 in
                  uu____16010 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16045 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16045 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16048 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16048
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16049;
                     FStar_TypeChecker_Env.mtarget = uu____16050;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16051;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16062;
                     FStar_TypeChecker_Env.mtarget = uu____16063;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16064;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16082 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16082)
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
                (fun uu____16138  ->
                   match uu____16138 with
                   | (a,imp) ->
                       let uu____16149 = norm cfg env [] a in
                       (uu____16149, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___254_16166 = comp1 in
            let uu____16169 =
              let uu____16170 =
                let uu____16179 = norm cfg env [] t in
                let uu____16180 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16179, uu____16180) in
              FStar_Syntax_Syntax.Total uu____16170 in
            {
              FStar_Syntax_Syntax.n = uu____16169;
              FStar_Syntax_Syntax.pos =
                (uu___254_16166.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___254_16166.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___255_16195 = comp1 in
            let uu____16198 =
              let uu____16199 =
                let uu____16208 = norm cfg env [] t in
                let uu____16209 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16208, uu____16209) in
              FStar_Syntax_Syntax.GTotal uu____16199 in
            {
              FStar_Syntax_Syntax.n = uu____16198;
              FStar_Syntax_Syntax.pos =
                (uu___255_16195.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___255_16195.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16261  ->
                      match uu____16261 with
                      | (a,i) ->
                          let uu____16272 = norm cfg env [] a in
                          (uu____16272, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___202_16283  ->
                      match uu___202_16283 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16287 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16287
                      | f -> f)) in
            let uu___256_16291 = comp1 in
            let uu____16294 =
              let uu____16295 =
                let uu___257_16296 = ct in
                let uu____16297 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16298 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16301 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16297;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___257_16296.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16298;
                  FStar_Syntax_Syntax.effect_args = uu____16301;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16295 in
            {
              FStar_Syntax_Syntax.n = uu____16294;
              FStar_Syntax_Syntax.pos =
                (uu___256_16291.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___256_16291.FStar_Syntax_Syntax.vars)
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
            (let uu___258_16319 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___258_16319.tcenv);
               delta_level = (uu___258_16319.delta_level);
               primitive_steps = (uu___258_16319.primitive_steps);
               strong = (uu___258_16319.strong)
             }) env [] t in
        let non_info t =
          let uu____16324 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16324 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16327 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___259_16346 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___259_16346.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___259_16346.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16353 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16353
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
                    let uu___260_16364 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___260_16364.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___260_16364.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___260_16364.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags1
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___261_16366 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___261_16366.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___261_16366.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___261_16366.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___261_16366.FStar_Syntax_Syntax.flags)
                    } in
              let uu___262_16367 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___262_16367.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___262_16367.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16369 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16372  ->
        match uu____16372 with
        | (x,imp) ->
            let uu____16375 =
              let uu___263_16376 = x in
              let uu____16377 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___263_16376.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___263_16376.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16377
              } in
            (uu____16375, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16383 =
          FStar_List.fold_left
            (fun uu____16401  ->
               fun b  ->
                 match uu____16401 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16383 with | (nbs,uu____16441) -> FStar_List.rev nbs
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
            let uu____16457 =
              let uu___264_16458 = rc in
              let uu____16459 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___264_16458.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16459;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___264_16458.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16457
        | uu____16466 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16479  ->
               let uu____16480 = FStar_Syntax_Print.tag_of_term t in
               let uu____16481 = FStar_Syntax_Print.term_to_string t in
               let uu____16482 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16489 =
                 let uu____16490 =
                   let uu____16493 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16493 in
                 stack_to_string uu____16490 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16480 uu____16481 uu____16482 uu____16489);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16522 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16522
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16524 =
                     let uu____16525 =
                       let uu____16526 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16526 in
                     FStar_Util.string_of_int uu____16525 in
                   let uu____16531 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16532 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16524 uu____16531 uu____16532
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___265_16550 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___265_16550.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___265_16550.strong)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16591  ->
                     let uu____16592 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16592);
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
               let uu____16628 =
                 let uu___266_16629 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___266_16629.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___266_16629.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16628
           | (Arg (Univ uu____16630,uu____16631,uu____16632))::uu____16633 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16636,uu____16637))::uu____16638 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16654),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16707  ->
                     let uu____16708 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16708);
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
                  (let uu____16718 = FStar_ST.op_Bang m in
                   match uu____16718 with
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
                   | FStar_Pervasives_Native.Some (uu____16862,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16905 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16905
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16917  ->
                     let uu____16918 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16918);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16923 =
                   log cfg
                     (fun uu____16928  ->
                        let uu____16929 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16930 =
                          let uu____16931 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16948  ->
                                    match uu____16948 with
                                    | (p,uu____16958,uu____16959) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16931
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16929 uu____16930);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___203_16976  ->
                                match uu___203_16976 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16977 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___267_16981 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___267_16981.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___267_16981.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17013 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17034 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17094  ->
                                    fun uu____17095  ->
                                      match (uu____17094, uu____17095) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17186 = norm_pat env3 p1 in
                                          (match uu____17186 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17034 with
                           | (pats1,env3) ->
                               ((let uu___268_17268 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___268_17268.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___269_17287 = x in
                            let uu____17288 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___269_17287.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___269_17287.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17288
                            } in
                          ((let uu___270_17302 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___270_17302.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___271_17313 = x in
                            let uu____17314 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___271_17313.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___271_17313.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17314
                            } in
                          ((let uu___272_17328 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___272_17328.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___273_17344 = x in
                            let uu____17345 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___273_17344.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___273_17344.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17345
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___274_17352 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___274_17352.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17362 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17376 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17376 with
                                  | (p,wopt,e) ->
                                      let uu____17396 = norm_pat env1 p in
                                      (match uu____17396 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17421 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17421 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17427 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17427) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17437) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17442 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17443;
                         FStar_Syntax_Syntax.fv_delta = uu____17444;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17445;
                         FStar_Syntax_Syntax.fv_delta = uu____17446;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17447);_}
                       -> true
                   | uu____17454 -> false in
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
                   let uu____17599 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17599 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17686 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17725 ->
                                 let uu____17726 =
                                   let uu____17727 = is_cons head1 in
                                   Prims.op_Negation uu____17727 in
                                 FStar_Util.Inr uu____17726)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17752 =
                              let uu____17753 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17753.FStar_Syntax_Syntax.n in
                            (match uu____17752 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17771 ->
                                 let uu____17772 =
                                   let uu____17773 = is_cons head1 in
                                   Prims.op_Negation uu____17773 in
                                 FStar_Util.Inr uu____17772))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17842)::rest_a,(p1,uu____17845)::rest_p) ->
                       let uu____17889 = matches_pat t1 p1 in
                       (match uu____17889 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17938 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18044 = matches_pat scrutinee1 p1 in
                       (match uu____18044 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18084  ->
                                  let uu____18085 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18086 =
                                    let uu____18087 =
                                      FStar_List.map
                                        (fun uu____18097  ->
                                           match uu____18097 with
                                           | (uu____18102,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18087
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18085 uu____18086);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18133  ->
                                       match uu____18133 with
                                       | (bv,t1) ->
                                           let uu____18156 =
                                             let uu____18163 =
                                               let uu____18166 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18166 in
                                             let uu____18167 =
                                               let uu____18168 =
                                                 let uu____18199 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18199, false) in
                                               Clos uu____18168 in
                                             (uu____18163, uu____18167) in
                                           uu____18156 :: env2) env1 s in
                              let uu____18308 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18308))) in
                 let uu____18309 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18309
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___204_18330  ->
                match uu___204_18330 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18334 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18340 -> d in
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
            let uu___275_18365 = config s e in
            {
              steps = (uu___275_18365.steps);
              tcenv = (uu___275_18365.tcenv);
              delta_level = (uu___275_18365.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___275_18365.strong)
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
      fun t  -> let uu____18390 = config s e in norm_comp uu____18390 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18403 = config [] env in norm_universe uu____18403 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18416 = config [] env in ghost_to_pure_aux uu____18416 [] c
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
        let uu____18434 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18434 in
      let uu____18441 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18441
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___276_18443 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___276_18443.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___276_18443.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18446  ->
                    let uu____18447 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18447))
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
            ((let uu____18464 =
                let uu____18469 =
                  let uu____18470 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18470 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18469) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18464);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18481 = config [AllowUnboundUniverses] env in
          norm_comp uu____18481 [] c
        with
        | e ->
            ((let uu____18494 =
                let uu____18499 =
                  let uu____18500 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18500 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18499) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18494);
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
                   let uu____18537 =
                     let uu____18538 =
                       let uu____18545 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18545) in
                     FStar_Syntax_Syntax.Tm_refine uu____18538 in
                   mk uu____18537 t01.FStar_Syntax_Syntax.pos
               | uu____18550 -> t2)
          | uu____18551 -> t2 in
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
        let uu____18591 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18591 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18620 ->
                 let uu____18627 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18627 with
                  | (actuals,uu____18637,uu____18638) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18652 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18652 with
                         | (binders,args) ->
                             let uu____18669 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18669
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
      | uu____18677 ->
          let uu____18678 = FStar_Syntax_Util.head_and_args t in
          (match uu____18678 with
           | (head1,args) ->
               let uu____18715 =
                 let uu____18716 = FStar_Syntax_Subst.compress head1 in
                 uu____18716.FStar_Syntax_Syntax.n in
               (match uu____18715 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18719,thead) ->
                    let uu____18745 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18745 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18787 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___281_18795 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___281_18795.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___281_18795.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___281_18795.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___281_18795.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___281_18795.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___281_18795.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___281_18795.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___281_18795.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___281_18795.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___281_18795.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___281_18795.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___281_18795.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___281_18795.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___281_18795.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___281_18795.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___281_18795.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___281_18795.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___281_18795.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___281_18795.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___281_18795.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___281_18795.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___281_18795.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___281_18795.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___281_18795.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___281_18795.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___281_18795.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___281_18795.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___281_18795.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___281_18795.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___281_18795.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___281_18795.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18787 with
                            | (uu____18796,ty,uu____18798) ->
                                eta_expand_with_type env t ty))
                | uu____18799 ->
                    let uu____18800 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___282_18808 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___282_18808.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___282_18808.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___282_18808.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___282_18808.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___282_18808.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___282_18808.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___282_18808.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___282_18808.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___282_18808.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___282_18808.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___282_18808.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___282_18808.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___282_18808.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___282_18808.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___282_18808.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___282_18808.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___282_18808.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___282_18808.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___282_18808.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___282_18808.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___282_18808.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___282_18808.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___282_18808.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___282_18808.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___282_18808.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___282_18808.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___282_18808.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___282_18808.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___282_18808.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___282_18808.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___282_18808.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18800 with
                     | (uu____18809,ty,uu____18811) ->
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
            | (uu____18885,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18891,FStar_Util.Inl t) ->
                let uu____18897 =
                  let uu____18900 =
                    let uu____18901 =
                      let uu____18914 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18914) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18901 in
                  FStar_Syntax_Syntax.mk uu____18900 in
                uu____18897 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18918 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18918 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18945 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19000 ->
                    let uu____19001 =
                      let uu____19010 =
                        let uu____19011 = FStar_Syntax_Subst.compress t3 in
                        uu____19011.FStar_Syntax_Syntax.n in
                      (uu____19010, tc) in
                    (match uu____19001 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19036) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19073) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19112,FStar_Util.Inl uu____19113) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19136 -> failwith "Impossible") in
              (match uu____18945 with
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
          let uu____19241 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19241 with
          | (univ_names1,binders1,tc) ->
              let uu____19299 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19299)
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
          let uu____19334 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19334 with
          | (univ_names1,binders1,tc) ->
              let uu____19394 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19394)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19427 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19427 with
           | (univ_names1,binders1,typ1) ->
               let uu___283_19455 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_19455.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_19455.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_19455.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_19455.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___284_19476 = s in
          let uu____19477 =
            let uu____19478 =
              let uu____19487 = FStar_List.map (elim_uvars env) sigs in
              (uu____19487, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19478 in
          {
            FStar_Syntax_Syntax.sigel = uu____19477;
            FStar_Syntax_Syntax.sigrng =
              (uu___284_19476.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___284_19476.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___284_19476.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___284_19476.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19504 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19504 with
           | (univ_names1,uu____19522,typ1) ->
               let uu___285_19536 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___285_19536.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___285_19536.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___285_19536.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___285_19536.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19542 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19542 with
           | (univ_names1,uu____19560,typ1) ->
               let uu___286_19574 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___286_19574.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___286_19574.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___286_19574.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___286_19574.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19608 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19608 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19631 =
                            let uu____19632 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19632 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19631 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___287_19635 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___287_19635.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___287_19635.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___288_19636 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___288_19636.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___288_19636.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___288_19636.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___288_19636.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___289_19648 = s in
          let uu____19649 =
            let uu____19650 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19650 in
          {
            FStar_Syntax_Syntax.sigel = uu____19649;
            FStar_Syntax_Syntax.sigrng =
              (uu___289_19648.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___289_19648.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___289_19648.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___289_19648.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19654 = elim_uvars_aux_t env us [] t in
          (match uu____19654 with
           | (us1,uu____19672,t1) ->
               let uu___290_19686 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___290_19686.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___290_19686.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___290_19686.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___290_19686.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19687 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19689 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19689 with
           | (univs1,binders,signature) ->
               let uu____19717 =
                 let uu____19726 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19726 with
                 | (univs_opening,univs2) ->
                     let uu____19753 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19753) in
               (match uu____19717 with
                | (univs_opening,univs_closing) ->
                    let uu____19770 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19776 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19777 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19776, uu____19777) in
                    (match uu____19770 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19799 =
                           match uu____19799 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19817 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19817 with
                                | (us1,t1) ->
                                    let uu____19828 =
                                      let uu____19833 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19840 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19833, uu____19840) in
                                    (match uu____19828 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19853 =
                                           let uu____19858 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19867 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19858, uu____19867) in
                                         (match uu____19853 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19883 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19883 in
                                              let uu____19884 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19884 with
                                               | (uu____19905,uu____19906,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19921 =
                                                       let uu____19922 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19922 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19921 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19927 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19927 with
                           | (uu____19940,uu____19941,t1) -> t1 in
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
                             | uu____20001 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20018 =
                               let uu____20019 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20019.FStar_Syntax_Syntax.n in
                             match uu____20018 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20078 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20107 =
                               let uu____20108 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20108.FStar_Syntax_Syntax.n in
                             match uu____20107 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20129) ->
                                 let uu____20150 = destruct_action_body body in
                                 (match uu____20150 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20195 ->
                                 let uu____20196 = destruct_action_body t in
                                 (match uu____20196 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20245 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20245 with
                           | (action_univs,t) ->
                               let uu____20254 = destruct_action_typ_templ t in
                               (match uu____20254 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___291_20295 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___291_20295.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___291_20295.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___292_20297 = ed in
                           let uu____20298 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20299 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20300 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20301 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20302 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20303 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20304 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20305 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20306 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20307 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20308 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20309 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20310 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20311 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___292_20297.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___292_20297.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20298;
                             FStar_Syntax_Syntax.bind_wp = uu____20299;
                             FStar_Syntax_Syntax.if_then_else = uu____20300;
                             FStar_Syntax_Syntax.ite_wp = uu____20301;
                             FStar_Syntax_Syntax.stronger = uu____20302;
                             FStar_Syntax_Syntax.close_wp = uu____20303;
                             FStar_Syntax_Syntax.assert_p = uu____20304;
                             FStar_Syntax_Syntax.assume_p = uu____20305;
                             FStar_Syntax_Syntax.null_wp = uu____20306;
                             FStar_Syntax_Syntax.trivial = uu____20307;
                             FStar_Syntax_Syntax.repr = uu____20308;
                             FStar_Syntax_Syntax.return_repr = uu____20309;
                             FStar_Syntax_Syntax.bind_repr = uu____20310;
                             FStar_Syntax_Syntax.actions = uu____20311
                           } in
                         let uu___293_20314 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___293_20314.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___293_20314.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___293_20314.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___293_20314.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___205_20331 =
            match uu___205_20331 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20358 = elim_uvars_aux_t env us [] t in
                (match uu____20358 with
                 | (us1,uu____20382,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___294_20401 = sub_eff in
            let uu____20402 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20405 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___294_20401.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___294_20401.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20402;
              FStar_Syntax_Syntax.lift = uu____20405
            } in
          let uu___295_20408 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___295_20408.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___295_20408.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___295_20408.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___295_20408.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20418 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20418 with
           | (univ_names1,binders1,comp1) ->
               let uu___296_20452 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___296_20452.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___296_20452.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___296_20452.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___296_20452.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20463 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t