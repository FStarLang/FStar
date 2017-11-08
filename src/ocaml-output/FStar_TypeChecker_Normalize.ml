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
              FStar_List.map (fun _0_41  -> FStar_Syntax_Syntax.U_succ _0_41)
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
                           (let uu___309_2733 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___309_2733.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___309_2733.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2721)) in
                  (match uu____2691 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___310_2749 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___310_2749.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___310_2749.FStar_Syntax_Syntax.lbeff);
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
                           (let uu___311_2898 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___311_2898.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___311_2898.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_42  -> FStar_Util.Inl _0_42)) in
                    let uu___312_2899 = lb in
                    let uu____2900 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___312_2899.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___312_2899.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___313_3329 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___313_3329.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___314_3348 = x in
                                let uu____3349 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___314_3348.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___314_3348.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3349
                                } in
                              ((let uu___315_3363 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___315_3363.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___316_3374 = x in
                                let uu____3375 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___316_3374.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___316_3374.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3375
                                } in
                              ((let uu___317_3389 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___317_3389.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___318_3405 = x in
                                let uu____3406 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___318_3405.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___318_3405.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3406
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___319_3413 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___319_3413.FStar_Syntax_Syntax.p)
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
                          let uu___320_3757 = b in
                          let uu____3758 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___320_3757.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___320_3757.FStar_Syntax_Syntax.index);
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
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___291_3905  ->
                           match uu___291_3905 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3909 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3909
                           | f -> f)) in
                 let uu____3913 =
                   let uu___321_3914 = c1 in
                   let uu____3915 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3915;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___321_3914.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3913)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___292_3925  ->
            match uu___292_3925 with
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
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___293_3947  ->
                      match uu___293_3947 with
                      | FStar_Syntax_Syntax.DECREASES uu____3948 -> false
                      | uu____3951 -> true)) in
            let rc1 =
              let uu___322_3953 = rc in
              let uu____3954 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___322_3953.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3954;
                FStar_Syntax_Syntax.residual_flags = flags
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
    let uu____4049 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4049 in
  let arg_as_bounded_int uu____4077 =
    match uu____4077 with
    | (a,uu____4089) ->
        let uu____4096 =
          let uu____4097 = FStar_Syntax_Subst.compress a in
          uu____4097.FStar_Syntax_Syntax.n in
        (match uu____4096 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4107;
                FStar_Syntax_Syntax.vars = uu____4108;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4110;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4111;_},uu____4112)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4151 =
               let uu____4156 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4156) in
             FStar_Pervasives_Native.Some uu____4151
         | uu____4161 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4203 = f a in FStar_Pervasives_Native.Some uu____4203
    | uu____4204 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4254 = f a0 a1 in FStar_Pervasives_Native.Some uu____4254
    | uu____4255 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4304 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4304 in
  let binary_op as_a f res args =
    let uu____4360 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4360 in
  let as_primitive_step uu____4384 =
    match uu____4384 with
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
           let uu____4432 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4432) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4460 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4460) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4481 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4481) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4509 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4509) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4537 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4537) in
  let list_of_string' rng s =
    let name l =
      let uu____4551 =
        let uu____4552 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4552 in
      mk uu____4551 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4562 =
      let uu____4565 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4565 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4562 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4595 =
      let uu____4596 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4596 in
    FStar_Syntax_Embeddings.embed_int rng uu____4595 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4614 = arg_as_string a1 in
        (match uu____4614 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4620 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4620 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4633 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4633
              | uu____4634 -> FStar_Pervasives_Native.None)
         | uu____4639 -> FStar_Pervasives_Native.None)
    | uu____4642 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4652 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4652 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4676 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4687 =
          let uu____4708 = arg_as_string fn in
          let uu____4711 = arg_as_int from_line in
          let uu____4714 = arg_as_int from_col in
          let uu____4717 = arg_as_int to_line in
          let uu____4720 = arg_as_int to_col in
          (uu____4708, uu____4711, uu____4714, uu____4717, uu____4720) in
        (match uu____4687 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4751 =
                 let uu____4752 = FStar_BigInt.to_int_fs from_l in
                 let uu____4753 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4752 uu____4753 in
               let uu____4754 =
                 let uu____4755 = FStar_BigInt.to_int_fs to_l in
                 let uu____4756 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4755 uu____4756 in
               FStar_Range.mk_range fn1 uu____4751 uu____4754 in
             let uu____4757 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4757
         | uu____4762 -> FStar_Pervasives_Native.None)
    | uu____4783 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4810)::(a1,uu____4812)::(a2,uu____4814)::[] ->
        let uu____4851 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4851 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4864 -> FStar_Pervasives_Native.None)
    | uu____4865 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4892)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4901 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____4925 =
      let uu____4940 =
        let uu____4955 =
          let uu____4970 =
            let uu____4985 =
              let uu____5000 =
                let uu____5015 =
                  let uu____5030 =
                    let uu____5045 =
                      let uu____5060 =
                        let uu____5075 =
                          let uu____5090 =
                            let uu____5105 =
                              let uu____5120 =
                                let uu____5135 =
                                  let uu____5150 =
                                    let uu____5165 =
                                      let uu____5180 =
                                        let uu____5195 =
                                          let uu____5210 =
                                            let uu____5223 =
                                              FStar_Parser_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____5223,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____5230 =
                                            let uu____5245 =
                                              let uu____5258 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____5258,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list
                                                      FStar_Syntax_Embeddings.unembed_char_safe)
                                                   string_of_list')) in
                                            let uu____5267 =
                                              let uu____5282 =
                                                let uu____5297 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____5297,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              let uu____5306 =
                                                let uu____5323 =
                                                  let uu____5338 =
                                                    FStar_Parser_Const.p2l
                                                      ["Prims"; "mk_range"] in
                                                  (uu____5338,
                                                    (Prims.parse_int "5"),
                                                    mk_range1) in
                                                let uu____5347 =
                                                  let uu____5364 =
                                                    let uu____5383 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "Range";
                                                        "prims_to_fstar_range"] in
                                                    (uu____5383,
                                                      (Prims.parse_int "1"),
                                                      idstep) in
                                                  [uu____5364] in
                                                uu____5323 :: uu____5347 in
                                              uu____5282 :: uu____5306 in
                                            uu____5245 :: uu____5267 in
                                          uu____5210 :: uu____5230 in
                                        (FStar_Parser_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____5195 in
                                      (FStar_Parser_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____5180 in
                                    (FStar_Parser_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____5165 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____5150 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____5135 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5120 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5105 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5090 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5075 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5060 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5719 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5719)))
                      :: uu____5045 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5745 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5745)))
                    :: uu____5030 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5771 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5771)))
                  :: uu____5015 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5797 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5797)))
                :: uu____5000 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____4985 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____4970 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____4955 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____4940 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____4925 in
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
      let uu____5947 =
        let uu____5948 =
          let uu____5949 = FStar_Syntax_Syntax.as_arg c in [uu____5949] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5948 in
      uu____5947 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____5984 =
              let uu____5997 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____5997, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6017  ->
                        fun uu____6018  ->
                          match (uu____6017, uu____6018) with
                          | ((int_to_t1,x),(uu____6037,y)) ->
                              let uu____6047 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6047))) in
            let uu____6048 =
              let uu____6063 =
                let uu____6076 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6076, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6096  ->
                          fun uu____6097  ->
                            match (uu____6096, uu____6097) with
                            | ((int_to_t1,x),(uu____6116,y)) ->
                                let uu____6126 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6126))) in
              let uu____6127 =
                let uu____6142 =
                  let uu____6155 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6155, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6175  ->
                            fun uu____6176  ->
                              match (uu____6175, uu____6176) with
                              | ((int_to_t1,x),(uu____6195,y)) ->
                                  let uu____6205 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6205))) in
                [uu____6142] in
              uu____6063 :: uu____6127 in
            uu____5984 :: uu____6048)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6295)::(a1,uu____6297)::(a2,uu____6299)::[] ->
        let uu____6336 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6336 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___323_6342 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___323_6342.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___323_6342.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___324_6346 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___324_6346.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___324_6346.FStar_Syntax_Syntax.vars)
                })
         | uu____6347 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6349)::uu____6350::(a1,uu____6352)::(a2,uu____6354)::[] ->
        let uu____6403 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6403 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___323_6409 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___323_6409.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___323_6409.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___324_6413 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___324_6413.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___324_6413.FStar_Syntax_Syntax.vars)
                })
         | uu____6414 -> FStar_Pervasives_Native.None)
    | uu____6415 -> failwith "Unexpected number of arguments" in
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
      let uu____6434 =
        let uu____6435 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6435 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6434
    with | uu____6441 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6445 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6445) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6505  ->
           fun subst1  ->
             match uu____6505 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6547)) ->
                      let uu____6606 = b in
                      (match uu____6606 with
                       | (bv,uu____6614) ->
                           let uu____6615 =
                             let uu____6616 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6616 in
                           if uu____6615
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6621 = unembed_binder term1 in
                              match uu____6621 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6628 =
                                      let uu___327_6629 = bv in
                                      let uu____6630 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___327_6629.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___327_6629.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6630
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6628 in
                                  let b_for_x =
                                    let uu____6634 =
                                      let uu____6641 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6641) in
                                    FStar_Syntax_Syntax.NT uu____6634 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___294_6650  ->
                                         match uu___294_6650 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6651,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6653;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6654;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6659 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6660 -> subst1)) env []
let reduce_primops:
  'Auu____6677 'Auu____6678 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6678) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6677 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____6719 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6719
          then tm
          else
            (let uu____6721 = FStar_Syntax_Util.head_and_args tm in
             match uu____6721 with
             | (head1,args) ->
                 let uu____6758 =
                   let uu____6759 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6759.FStar_Syntax_Syntax.n in
                 (match uu____6758 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6763 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6763 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6780  ->
                                   let uu____6781 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6782 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6789 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6781 uu____6782 uu____6789);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6794  ->
                                   let uu____6795 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6795);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6798  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6800 =
                                 prim_step.interpretation psc args in
                               match uu____6800 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6806  ->
                                         let uu____6807 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6807);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6813  ->
                                         let uu____6814 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6815 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6814 uu____6815);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6816 ->
                           (log_primops cfg
                              (fun uu____6820  ->
                                 let uu____6821 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6821);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6825  ->
                            let uu____6826 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6826);
                       (match args with
                        | (a1,uu____6828)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6845 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6857  ->
                            let uu____6858 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6858);
                       (match args with
                        | (a1,uu____6860)::(a2,uu____6862)::[] ->
                            let uu____6889 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____6889 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___328_6893 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___328_6893.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___328_6893.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6896 -> tm))
                  | uu____6905 -> tm))
let reduce_equality:
  'Auu____6910 'Auu____6911 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6911) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6910 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___329_6949 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___329_6949.tcenv);
           delta_level = (uu___329_6949.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___329_6949.strong)
         }) tm
let maybe_simplify:
  'Auu____6956 'Auu____6957 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6957) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6956 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____6999 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____6999
          then tm1
          else
            (let w t =
               let uu___330_7011 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___330_7011.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___330_7011.FStar_Syntax_Syntax.vars)
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
               | uu____7028 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7068;
                         FStar_Syntax_Syntax.vars = uu____7069;_},uu____7070);
                    FStar_Syntax_Syntax.pos = uu____7071;
                    FStar_Syntax_Syntax.vars = uu____7072;_},args)
                 ->
                 let uu____7098 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7098
                 then
                   let uu____7099 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7099 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7154)::
                        (uu____7155,(arg,uu____7157))::[] -> arg
                    | (uu____7222,(arg,uu____7224))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7225)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7290)::uu____7291::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7354::(FStar_Pervasives_Native.Some (false
                                   ),uu____7355)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7418 -> tm1)
                 else
                   (let uu____7434 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7434
                    then
                      let uu____7435 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7435 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7490)::uu____7491::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7554::(FStar_Pervasives_Native.Some (true
                                     ),uu____7555)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7618)::
                          (uu____7619,(arg,uu____7621))::[] -> arg
                      | (uu____7686,(arg,uu____7688))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7689)::[]
                          -> arg
                      | uu____7754 -> tm1
                    else
                      (let uu____7770 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7770
                       then
                         let uu____7771 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7771 with
                         | uu____7826::(FStar_Pervasives_Native.Some (true
                                        ),uu____7827)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____7890)::uu____7891::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____7954)::
                             (uu____7955,(arg,uu____7957))::[] -> arg
                         | (uu____8022,(p,uu____8024))::(uu____8025,(q,uu____8027))::[]
                             ->
                             let uu____8092 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8092
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8094 -> tm1
                       else
                         (let uu____8110 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8110
                          then
                            let uu____8111 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8111 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8166)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8205)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8244 -> tm1
                          else
                            (let uu____8260 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8260
                             then
                               match args with
                               | (t,uu____8262)::[] ->
                                   let uu____8279 =
                                     let uu____8280 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8280.FStar_Syntax_Syntax.n in
                                   (match uu____8279 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8283::[],body,uu____8285) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8312 -> tm1)
                                    | uu____8315 -> tm1)
                               | (uu____8316,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8317))::
                                   (t,uu____8319)::[] ->
                                   let uu____8358 =
                                     let uu____8359 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8359.FStar_Syntax_Syntax.n in
                                   (match uu____8358 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8362::[],body,uu____8364) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8391 -> tm1)
                                    | uu____8394 -> tm1)
                               | uu____8395 -> tm1
                             else
                               (let uu____8405 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8405
                                then
                                  match args with
                                  | (t,uu____8407)::[] ->
                                      let uu____8424 =
                                        let uu____8425 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8425.FStar_Syntax_Syntax.n in
                                      (match uu____8424 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8428::[],body,uu____8430)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8457 -> tm1)
                                       | uu____8460 -> tm1)
                                  | (uu____8461,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8462))::(t,uu____8464)::[] ->
                                      let uu____8503 =
                                        let uu____8504 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8504.FStar_Syntax_Syntax.n in
                                      (match uu____8503 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8507::[],body,uu____8509)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8536 -> tm1)
                                       | uu____8539 -> tm1)
                                  | uu____8540 -> tm1
                                else
                                  (let uu____8550 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8550
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8551;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8552;_},uu____8553)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8570;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8571;_},uu____8572)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8589 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8600;
                    FStar_Syntax_Syntax.vars = uu____8601;_},args)
                 ->
                 let uu____8623 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8623
                 then
                   let uu____8624 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8624 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8679)::
                        (uu____8680,(arg,uu____8682))::[] -> arg
                    | (uu____8747,(arg,uu____8749))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8750)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8815)::uu____8816::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8879::(FStar_Pervasives_Native.Some (false
                                   ),uu____8880)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8943 -> tm1)
                 else
                   (let uu____8959 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8959
                    then
                      let uu____8960 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8960 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9015)::uu____9016::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9079::(FStar_Pervasives_Native.Some (true
                                     ),uu____9080)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9143)::
                          (uu____9144,(arg,uu____9146))::[] -> arg
                      | (uu____9211,(arg,uu____9213))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9214)::[]
                          -> arg
                      | uu____9279 -> tm1
                    else
                      (let uu____9295 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9295
                       then
                         let uu____9296 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9296 with
                         | uu____9351::(FStar_Pervasives_Native.Some (true
                                        ),uu____9352)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9415)::uu____9416::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9479)::
                             (uu____9480,(arg,uu____9482))::[] -> arg
                         | (uu____9547,(p,uu____9549))::(uu____9550,(q,uu____9552))::[]
                             ->
                             let uu____9617 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9617
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9619 -> tm1
                       else
                         (let uu____9635 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9635
                          then
                            let uu____9636 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9636 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9691)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9730)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9769 -> tm1
                          else
                            (let uu____9785 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9785
                             then
                               match args with
                               | (t,uu____9787)::[] ->
                                   let uu____9804 =
                                     let uu____9805 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9805.FStar_Syntax_Syntax.n in
                                   (match uu____9804 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9808::[],body,uu____9810) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9837 -> tm1)
                                    | uu____9840 -> tm1)
                               | (uu____9841,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9842))::
                                   (t,uu____9844)::[] ->
                                   let uu____9883 =
                                     let uu____9884 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9884.FStar_Syntax_Syntax.n in
                                   (match uu____9883 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9887::[],body,uu____9889) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9916 -> tm1)
                                    | uu____9919 -> tm1)
                               | uu____9920 -> tm1
                             else
                               (let uu____9930 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9930
                                then
                                  match args with
                                  | (t,uu____9932)::[] ->
                                      let uu____9949 =
                                        let uu____9950 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9950.FStar_Syntax_Syntax.n in
                                      (match uu____9949 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9953::[],body,uu____9955)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9982 -> tm1)
                                       | uu____9985 -> tm1)
                                  | (uu____9986,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9987))::(t,uu____9989)::[] ->
                                      let uu____10028 =
                                        let uu____10029 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10029.FStar_Syntax_Syntax.n in
                                      (match uu____10028 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10032::[],body,uu____10034)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10061 -> tm1)
                                       | uu____10064 -> tm1)
                                  | uu____10065 -> tm1
                                else
                                  (let uu____10075 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10075
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10076;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10077;_},uu____10078)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10095;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10096;_},uu____10097)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10114 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | uu____10124 -> tm1)
let is_norm_request:
  'Auu____10128 .
    FStar_Syntax_Syntax.term -> 'Auu____10128 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10141 =
        let uu____10148 =
          let uu____10149 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10149.FStar_Syntax_Syntax.n in
        (uu____10148, args) in
      match uu____10141 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10155::uu____10156::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10160::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10165::uu____10166::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10169 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___295_10180  ->
    match uu___295_10180 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10186 =
          let uu____10189 =
            let uu____10190 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10190 in
          [uu____10189] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10186
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10205 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10205) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10243 =
          let uu____10246 =
            let uu____10251 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10251 s in
          FStar_All.pipe_right uu____10246 FStar_Util.must in
        FStar_All.pipe_right uu____10243 tr_norm_steps in
      match args with
      | uu____10276::(tm,uu____10278)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10301)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10316)::uu____10317::(tm,uu____10319)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10359 =
              let uu____10362 = full_norm steps in parse_steps uu____10362 in
            Beta :: uu____10359 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10371 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___296_10388  ->
    match uu___296_10388 with
    | (App
        (uu____10391,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10392;
                       FStar_Syntax_Syntax.vars = uu____10393;_},uu____10394,uu____10395))::uu____10396
        -> true
    | uu____10403 -> false
let firstn:
  'Auu____10409 .
    Prims.int ->
      'Auu____10409 Prims.list ->
        ('Auu____10409 Prims.list,'Auu____10409 Prims.list)
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
          (uu____10445,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10446;
                         FStar_Syntax_Syntax.vars = uu____10447;_},uu____10448,uu____10449))::uu____10450
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10457 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10573  ->
               let uu____10574 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10575 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10576 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10583 =
                 let uu____10584 =
                   let uu____10587 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10587 in
                 stack_to_string uu____10584 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10574 uu____10575 uu____10576 uu____10583);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10610 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10635 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10652 =
                 let uu____10653 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10654 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10653 uu____10654 in
               failwith uu____10652
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10655 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10672 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10673 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10674;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10675;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10678;
                 FStar_Syntax_Syntax.fv_delta = uu____10679;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10680;
                 FStar_Syntax_Syntax.fv_delta = uu____10681;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10682);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10690 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10690 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10696  ->
                     let uu____10697 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10698 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10697 uu____10698);
                if b
                then
                  (let uu____10699 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10699 t1 fv)
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
                 let uu___331_10738 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___331_10738.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___331_10738.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10771 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10771) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___332_10779 = cfg in
                 let uu____10780 =
                   FStar_List.filter
                     (fun uu___297_10783  ->
                        match uu___297_10783 with
                        | UnfoldOnly uu____10784 -> false
                        | NoDeltaSteps  -> false
                        | uu____10787 -> true) cfg.steps in
                 {
                   steps = uu____10780;
                   tcenv = (uu___332_10779.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___332_10779.primitive_steps);
                   strong = (uu___332_10779.strong)
                 } in
               let uu____10788 = get_norm_request (norm cfg' env []) args in
               (match uu____10788 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10804 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___298_10809  ->
                                match uu___298_10809 with
                                | UnfoldUntil uu____10810 -> true
                                | UnfoldOnly uu____10811 -> true
                                | uu____10814 -> false)) in
                      if uu____10804
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___333_10819 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___333_10819.tcenv);
                        delta_level;
                        primitive_steps = (uu___333_10819.primitive_steps);
                        strong = (uu___333_10819.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10830 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10830
                      then
                        let uu____10833 =
                          let uu____10834 =
                            let uu____10839 = FStar_Util.now () in
                            (t1, uu____10839) in
                          Debug uu____10834 in
                        uu____10833 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____10841;
                  FStar_Syntax_Syntax.vars = uu____10842;_},a1::a2::rest)
               ->
               let uu____10890 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10890 with
                | (hd1,uu____10906) ->
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
                  FStar_Syntax_Syntax.pos = uu____10971;
                  FStar_Syntax_Syntax.vars = uu____10972;_},a1::a2::rest)
               ->
               let uu____11020 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11020 with
                | (hd1,uu____11036) ->
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
                  FStar_Syntax_Syntax.pos = uu____11101;
                  FStar_Syntax_Syntax.vars = uu____11102;_},a1::a2::a3::rest)
               ->
               let uu____11163 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11163 with
                | (hd1,uu____11179) ->
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
                    (FStar_Const.Const_reflect uu____11250);
                  FStar_Syntax_Syntax.pos = uu____11251;
                  FStar_Syntax_Syntax.vars = uu____11252;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11284 = FStar_List.tl stack1 in
               norm cfg env uu____11284 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11287;
                  FStar_Syntax_Syntax.vars = uu____11288;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11320 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11320 with
                | (reify_head,uu____11336) ->
                    let a1 =
                      let uu____11358 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11358 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11361);
                            FStar_Syntax_Syntax.pos = uu____11362;
                            FStar_Syntax_Syntax.vars = uu____11363;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11397 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11407 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11407
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11414 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11414
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11417 =
                      let uu____11424 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11424, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11417 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___299_11437  ->
                         match uu___299_11437 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11440 =
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
                 if uu____11440
                 then false
                 else
                   (let uu____11442 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___300_11449  ->
                              match uu___300_11449 with
                              | UnfoldOnly uu____11450 -> true
                              | uu____11453 -> false)) in
                    match uu____11442 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11457 -> should_delta) in
               (log cfg
                  (fun uu____11465  ->
                     let uu____11466 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11467 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11468 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11466 uu____11467 uu____11468);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11471 = lookup_bvar env x in
               (match uu____11471 with
                | Univ uu____11474 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11523 = FStar_ST.op_Bang r in
                      (match uu____11523 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11660  ->
                                 let uu____11661 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11662 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11661
                                   uu____11662);
                            (let uu____11663 =
                               let uu____11664 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11664.FStar_Syntax_Syntax.n in
                             match uu____11663 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11667 ->
                                 norm cfg env2 stack1 t'
                             | uu____11684 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11742)::uu____11743 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11752)::uu____11753 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11763,uu____11764))::stack_rest ->
                    (match c with
                     | Univ uu____11768 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11777 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11798  ->
                                    let uu____11799 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11799);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11839  ->
                                    let uu____11840 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11840);
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
                      (let uu___334_11890 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___334_11890.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___334_11890.strong)
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11923  ->
                          let uu____11924 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11924);
                     norm cfg env stack2 t1)
                | (Debug uu____11925)::uu____11926 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11933 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11933
                    else
                      (let uu____11935 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11935 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11977  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12005 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12005
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12015 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12015)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12020 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12020.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12020.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12021 -> lopt in
                           (log cfg
                              (fun uu____12027  ->
                                 let uu____12028 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12028);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12041 = cfg in
                               {
                                 steps = (uu___336_12041.steps);
                                 tcenv = (uu___336_12041.tcenv);
                                 delta_level = (uu___336_12041.delta_level);
                                 primitive_steps =
                                   (uu___336_12041.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12052)::uu____12053 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12060 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12060
                    else
                      (let uu____12062 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12062 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12104  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12132 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12132
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12142 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12142)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12147 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12147.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12147.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12148 -> lopt in
                           (log cfg
                              (fun uu____12154  ->
                                 let uu____12155 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12155);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12168 = cfg in
                               {
                                 steps = (uu___336_12168.steps);
                                 tcenv = (uu___336_12168.tcenv);
                                 delta_level = (uu___336_12168.delta_level);
                                 primitive_steps =
                                   (uu___336_12168.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12179)::uu____12180 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12191 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12191
                    else
                      (let uu____12193 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12193 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12235  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12263 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12263
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12273 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12273)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12278 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12278.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12278.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12279 -> lopt in
                           (log cfg
                              (fun uu____12285  ->
                                 let uu____12286 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12286);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12299 = cfg in
                               {
                                 steps = (uu___336_12299.steps);
                                 tcenv = (uu___336_12299.tcenv);
                                 delta_level = (uu___336_12299.delta_level);
                                 primitive_steps =
                                   (uu___336_12299.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12310)::uu____12311 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12322 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12322
                    else
                      (let uu____12324 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12324 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12366  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12394 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12394
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12404 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12404)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12409 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12409.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12409.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12410 -> lopt in
                           (log cfg
                              (fun uu____12416  ->
                                 let uu____12417 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12417);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12430 = cfg in
                               {
                                 steps = (uu___336_12430.steps);
                                 tcenv = (uu___336_12430.tcenv);
                                 delta_level = (uu___336_12430.delta_level);
                                 primitive_steps =
                                   (uu___336_12430.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12441)::uu____12442 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12457 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12457
                    else
                      (let uu____12459 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12459 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12501  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12529 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12529
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12539 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12539)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12544 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12544.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12544.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12545 -> lopt in
                           (log cfg
                              (fun uu____12551  ->
                                 let uu____12552 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12552);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12565 = cfg in
                               {
                                 steps = (uu___336_12565.steps);
                                 tcenv = (uu___336_12565.tcenv);
                                 delta_level = (uu___336_12565.delta_level);
                                 primitive_steps =
                                   (uu___336_12565.primitive_steps);
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
                      let uu____12576 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12576
                    else
                      (let uu____12578 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12578 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12620  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12648 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12648
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12658 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12658)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12663 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12663.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12663.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12664 -> lopt in
                           (log cfg
                              (fun uu____12670  ->
                                 let uu____12671 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12671);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12684 = cfg in
                               {
                                 steps = (uu___336_12684.steps);
                                 tcenv = (uu___336_12684.tcenv);
                                 delta_level = (uu___336_12684.delta_level);
                                 primitive_steps =
                                   (uu___336_12684.primitive_steps);
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
                      (fun uu____12733  ->
                         fun stack2  ->
                           match uu____12733 with
                           | (a,aq) ->
                               let uu____12745 =
                                 let uu____12746 =
                                   let uu____12753 =
                                     let uu____12754 =
                                       let uu____12785 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12785, false) in
                                     Clos uu____12754 in
                                   (uu____12753, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12746 in
                               uu____12745 :: stack2) args) in
               (log cfg
                  (fun uu____12861  ->
                     let uu____12862 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12862);
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
                             ((let uu___337_12898 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___337_12898.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___337_12898.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12899 ->
                      let uu____12904 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12904)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12907 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12907 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12938 =
                          let uu____12939 =
                            let uu____12946 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___338_12948 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___338_12948.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___338_12948.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12946) in
                          FStar_Syntax_Syntax.Tm_refine uu____12939 in
                        mk uu____12938 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12967 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12967
               else
                 (let uu____12969 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12969 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12977 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13001  -> dummy :: env1) env) in
                        norm_comp cfg uu____12977 c1 in
                      let t2 =
                        let uu____13023 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13023 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13082)::uu____13083 ->
                    (log cfg
                       (fun uu____13094  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13095)::uu____13096 ->
                    (log cfg
                       (fun uu____13107  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13108,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13109;
                                   FStar_Syntax_Syntax.vars = uu____13110;_},uu____13111,uu____13112))::uu____13113
                    ->
                    (log cfg
                       (fun uu____13122  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13123)::uu____13124 ->
                    (log cfg
                       (fun uu____13135  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13136 ->
                    (log cfg
                       (fun uu____13139  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13143  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13160 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13160
                         | FStar_Util.Inr c ->
                             let uu____13168 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13168 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13174 =
                         let uu____13175 =
                           let uu____13176 =
                             let uu____13203 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13203, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13176 in
                         mk uu____13175 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13174))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13279,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13280;
                               FStar_Syntax_Syntax.lbunivs = uu____13281;
                               FStar_Syntax_Syntax.lbtyp = uu____13282;
                               FStar_Syntax_Syntax.lbeff = uu____13283;
                               FStar_Syntax_Syntax.lbdef = uu____13284;_}::uu____13285),uu____13286)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13322 =
                 (let uu____13325 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13325) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13327 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13327))) in
               if uu____13322
               then
                 let binder =
                   let uu____13329 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13329 in
                 let env1 =
                   let uu____13339 =
                     let uu____13346 =
                       let uu____13347 =
                         let uu____13378 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13378,
                           false) in
                       Clos uu____13347 in
                     ((FStar_Pervasives_Native.Some binder), uu____13346) in
                   uu____13339 :: env in
                 (log cfg
                    (fun uu____13463  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13465 =
                    let uu____13470 =
                      let uu____13471 =
                        let uu____13472 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13472
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13471] in
                    FStar_Syntax_Subst.open_term uu____13470 body in
                  match uu____13465 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13481  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13489 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13489 in
                          FStar_Util.Inl
                            (let uu___339_13499 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___339_13499.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___339_13499.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13502  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___340_13504 = lb in
                           let uu____13505 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___340_13504.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___340_13504.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13505
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13540  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___341_13560 = cfg in
                           {
                             steps = (uu___341_13560.steps);
                             tcenv = (uu___341_13560.tcenv);
                             delta_level = (uu___341_13560.delta_level);
                             primitive_steps =
                               (uu___341_13560.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13563  ->
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
               let uu____13580 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13580 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13616 =
                               let uu___342_13617 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___342_13617.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___342_13617.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13616 in
                           let uu____13618 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13618 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13644 =
                                   FStar_List.map (fun uu____13660  -> dummy)
                                     lbs1 in
                                 let uu____13661 =
                                   let uu____13670 =
                                     FStar_List.map
                                       (fun uu____13690  -> dummy) xs1 in
                                   FStar_List.append uu____13670 env in
                                 FStar_List.append uu____13644 uu____13661 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13714 =
                                       let uu___343_13715 = rc in
                                       let uu____13716 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___343_13715.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13716;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___343_13715.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13714
                                 | uu____13723 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___344_13727 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___344_13727.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___344_13727.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13737 =
                        FStar_List.map (fun uu____13753  -> dummy) lbs2 in
                      FStar_List.append uu____13737 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13761 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13761 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___345_13777 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___345_13777.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___345_13777.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13804 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13804
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13823 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13899  ->
                        match uu____13899 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___346_14020 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___346_14020.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___346_14020.FStar_Syntax_Syntax.sort)
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
               (match uu____13823 with
                | (rec_env,memos,uu____14217) ->
                    let uu____14270 =
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
                             let uu____14801 =
                               let uu____14808 =
                                 let uu____14809 =
                                   let uu____14840 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14840, false) in
                                 Clos uu____14809 in
                               (FStar_Pervasives_Native.None, uu____14808) in
                             uu____14801 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14945 =
                      let uu____14946 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14946 in
                    if uu____14945
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14956 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14956
                        then
                          let uu___347_14957 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___347_14957.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___347_14957.primitive_steps);
                            strong = (uu___347_14957.strong)
                          }
                        else
                          (let uu___348_14959 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___348_14959.tcenv);
                             delta_level = (uu___348_14959.delta_level);
                             primitive_steps =
                               (uu___348_14959.primitive_steps);
                             strong = (uu___348_14959.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14961 =
                         let uu____14962 = FStar_Syntax_Subst.compress head1 in
                         uu____14962.FStar_Syntax_Syntax.n in
                       match uu____14961 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14980 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14980 with
                            | (uu____14981,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14987 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14995 =
                                         let uu____14996 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14996.FStar_Syntax_Syntax.n in
                                       match uu____14995 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15002,uu____15003))
                                           ->
                                           let uu____15012 =
                                             let uu____15013 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15013.FStar_Syntax_Syntax.n in
                                           (match uu____15012 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15019,msrc,uu____15021))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15030 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15030
                                            | uu____15031 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15032 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15033 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15033 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___349_15038 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___349_15038.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___349_15038.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___349_15038.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15039 =
                                            FStar_List.tl stack1 in
                                          let uu____15040 =
                                            let uu____15041 =
                                              let uu____15044 =
                                                let uu____15045 =
                                                  let uu____15058 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15058) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15045 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15044 in
                                            uu____15041
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15039
                                            uu____15040
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15074 =
                                            let uu____15075 = is_return body in
                                            match uu____15075 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15079;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15080;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15085 -> false in
                                          if uu____15074
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
                                               let uu____15109 =
                                                 let uu____15112 =
                                                   let uu____15113 =
                                                     let uu____15130 =
                                                       let uu____15133 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15133] in
                                                     (uu____15130, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15113 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15112 in
                                               uu____15109
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15149 =
                                                 let uu____15150 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15150.FStar_Syntax_Syntax.n in
                                               match uu____15149 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15156::uu____15157::[])
                                                   ->
                                                   let uu____15164 =
                                                     let uu____15167 =
                                                       let uu____15168 =
                                                         let uu____15175 =
                                                           let uu____15178 =
                                                             let uu____15179
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15179 in
                                                           let uu____15180 =
                                                             let uu____15183
                                                               =
                                                               let uu____15184
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15184 in
                                                             [uu____15183] in
                                                           uu____15178 ::
                                                             uu____15180 in
                                                         (bind1, uu____15175) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15168 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15167 in
                                                   uu____15164
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15192 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15198 =
                                                 let uu____15201 =
                                                   let uu____15202 =
                                                     let uu____15217 =
                                                       let uu____15220 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15221 =
                                                         let uu____15224 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15225 =
                                                           let uu____15228 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15229 =
                                                             let uu____15232
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15233
                                                               =
                                                               let uu____15236
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15237
                                                                 =
                                                                 let uu____15240
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15240] in
                                                               uu____15236 ::
                                                                 uu____15237 in
                                                             uu____15232 ::
                                                               uu____15233 in
                                                           uu____15228 ::
                                                             uu____15229 in
                                                         uu____15224 ::
                                                           uu____15225 in
                                                       uu____15220 ::
                                                         uu____15221 in
                                                     (bind_inst, uu____15217) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15202 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15201 in
                                               uu____15198
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15248 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15248 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15272 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15272 with
                            | (uu____15273,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15308 =
                                        let uu____15309 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15309.FStar_Syntax_Syntax.n in
                                      match uu____15308 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15315) -> t4
                                      | uu____15320 -> head2 in
                                    let uu____15321 =
                                      let uu____15322 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15322.FStar_Syntax_Syntax.n in
                                    match uu____15321 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15328 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15329 = maybe_extract_fv head2 in
                                  match uu____15329 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15339 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15339
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15344 =
                                          maybe_extract_fv head3 in
                                        match uu____15344 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15349 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15350 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15355 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15370 =
                                    match uu____15370 with
                                    | (e,q) ->
                                        let uu____15377 =
                                          let uu____15378 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15378.FStar_Syntax_Syntax.n in
                                        (match uu____15377 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15393 -> false) in
                                  let uu____15394 =
                                    let uu____15395 =
                                      let uu____15402 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15402 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15395 in
                                  if uu____15394
                                  then
                                    let uu____15407 =
                                      let uu____15408 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15408 in
                                    failwith uu____15407
                                  else ());
                                 (let uu____15410 =
                                    maybe_unfold_action head_app in
                                  match uu____15410 with
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
                                      let uu____15449 = FStar_List.tl stack1 in
                                      norm cfg env uu____15449 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15463 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15463 in
                           let uu____15464 = FStar_List.tl stack1 in
                           norm cfg env uu____15464 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15585  ->
                                     match uu____15585 with
                                     | (pat,wopt,tm) ->
                                         let uu____15633 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15633))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15665 = FStar_List.tl stack1 in
                           norm cfg env uu____15665 tm
                       | uu____15666 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15674 = should_reify cfg stack1 in
                    if uu____15674
                    then
                      let uu____15675 = FStar_List.tl stack1 in
                      let uu____15676 =
                        let uu____15677 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15677 in
                      norm cfg env uu____15675 uu____15676
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15680 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15680
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___350_15689 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___350_15689.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___350_15689.primitive_steps);
                             strong = (uu___350_15689.strong)
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
                | uu____15691 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15693::uu____15694 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15699) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15700 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15731 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15745 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15745
                             | uu____15756 -> m in
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
              let uu____15768 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15768 in
            let uu____15769 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15769 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15782  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15793  ->
                      let uu____15794 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15795 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15794
                        uu____15795);
                 (let t1 =
                    let uu____15797 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15797
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
                    | (UnivArgs (us',uu____15807))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____15862 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15865 ->
                        let uu____15868 =
                          let uu____15869 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15869 in
                        failwith uu____15868
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
              let uu____15879 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15879 with
              | (uu____15880,return_repr) ->
                  let return_inst =
                    let uu____15889 =
                      let uu____15890 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15890.FStar_Syntax_Syntax.n in
                    match uu____15889 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15896::[]) ->
                        let uu____15903 =
                          let uu____15906 =
                            let uu____15907 =
                              let uu____15914 =
                                let uu____15917 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15917] in
                              (return_tm, uu____15914) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15907 in
                          FStar_Syntax_Syntax.mk uu____15906 in
                        uu____15903 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15925 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15928 =
                    let uu____15931 =
                      let uu____15932 =
                        let uu____15947 =
                          let uu____15950 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15951 =
                            let uu____15954 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15954] in
                          uu____15950 :: uu____15951 in
                        (return_inst, uu____15947) in
                      FStar_Syntax_Syntax.Tm_app uu____15932 in
                    FStar_Syntax_Syntax.mk uu____15931 in
                  uu____15928 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15963 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15963 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15966 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15966
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15967;
                     FStar_TypeChecker_Env.mtarget = uu____15968;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15969;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15980;
                     FStar_TypeChecker_Env.mtarget = uu____15981;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15982;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16000 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16000)
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
                (fun uu____16056  ->
                   match uu____16056 with
                   | (a,imp) ->
                       let uu____16067 = norm cfg env [] a in
                       (uu____16067, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___351_16084 = comp1 in
            let uu____16087 =
              let uu____16088 =
                let uu____16097 = norm cfg env [] t in
                let uu____16098 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16097, uu____16098) in
              FStar_Syntax_Syntax.Total uu____16088 in
            {
              FStar_Syntax_Syntax.n = uu____16087;
              FStar_Syntax_Syntax.pos =
                (uu___351_16084.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___351_16084.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___352_16113 = comp1 in
            let uu____16116 =
              let uu____16117 =
                let uu____16126 = norm cfg env [] t in
                let uu____16127 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16126, uu____16127) in
              FStar_Syntax_Syntax.GTotal uu____16117 in
            {
              FStar_Syntax_Syntax.n = uu____16116;
              FStar_Syntax_Syntax.pos =
                (uu___352_16113.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___352_16113.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16179  ->
                      match uu____16179 with
                      | (a,i) ->
                          let uu____16190 = norm cfg env [] a in
                          (uu____16190, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___301_16201  ->
                      match uu___301_16201 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16205 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16205
                      | f -> f)) in
            let uu___353_16209 = comp1 in
            let uu____16212 =
              let uu____16213 =
                let uu___354_16214 = ct in
                let uu____16215 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16216 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16219 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16215;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___354_16214.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16216;
                  FStar_Syntax_Syntax.effect_args = uu____16219;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16213 in
            {
              FStar_Syntax_Syntax.n = uu____16212;
              FStar_Syntax_Syntax.pos =
                (uu___353_16209.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___353_16209.FStar_Syntax_Syntax.vars)
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
            (let uu___355_16237 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___355_16237.tcenv);
               delta_level = (uu___355_16237.delta_level);
               primitive_steps = (uu___355_16237.primitive_steps);
               strong = (uu___355_16237.strong)
             }) env [] t in
        let non_info t =
          let uu____16242 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16242 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16245 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___356_16264 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___356_16264.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___356_16264.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16271 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16271
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
                    let uu___357_16282 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___357_16282.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___357_16282.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___357_16282.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___358_16284 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___358_16284.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___358_16284.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___358_16284.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___358_16284.FStar_Syntax_Syntax.flags)
                    } in
              let uu___359_16285 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___359_16285.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___359_16285.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16287 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16290  ->
        match uu____16290 with
        | (x,imp) ->
            let uu____16293 =
              let uu___360_16294 = x in
              let uu____16295 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___360_16294.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___360_16294.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16295
              } in
            (uu____16293, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16301 =
          FStar_List.fold_left
            (fun uu____16319  ->
               fun b  ->
                 match uu____16319 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16301 with | (nbs,uu____16359) -> FStar_List.rev nbs
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
            let uu____16375 =
              let uu___361_16376 = rc in
              let uu____16377 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___361_16376.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16377;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___361_16376.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16375
        | uu____16384 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16397  ->
               let uu____16398 = FStar_Syntax_Print.tag_of_term t in
               let uu____16399 = FStar_Syntax_Print.term_to_string t in
               let uu____16400 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16407 =
                 let uu____16408 =
                   let uu____16411 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16411 in
                 stack_to_string uu____16408 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16398 uu____16399 uu____16400 uu____16407);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16440 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16440
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16442 =
                     let uu____16443 =
                       let uu____16444 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16444 in
                     FStar_Util.string_of_int uu____16443 in
                   let uu____16449 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16450 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16442 uu____16449 uu____16450
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___362_16468 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___362_16468.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___362_16468.strong)
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16509  ->
                     let uu____16510 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16510);
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
               let uu____16546 =
                 let uu___363_16547 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___363_16547.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___363_16547.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16546
           | (Arg (Univ uu____16548,uu____16549,uu____16550))::uu____16551 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16554,uu____16555))::uu____16556 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16572),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16625  ->
                     let uu____16626 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16626);
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
                  (let uu____16636 = FStar_ST.op_Bang m in
                   match uu____16636 with
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
                   | FStar_Pervasives_Native.Some (uu____16780,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16823 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16823
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16835  ->
                     let uu____16836 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16836);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16841 =
                   log cfg
                     (fun uu____16846  ->
                        let uu____16847 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16848 =
                          let uu____16849 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16866  ->
                                    match uu____16866 with
                                    | (p,uu____16876,uu____16877) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16849
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16847 uu____16848);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___302_16894  ->
                                match uu___302_16894 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16895 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___364_16899 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___364_16899.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___364_16899.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16931 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16952 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17012  ->
                                    fun uu____17013  ->
                                      match (uu____17012, uu____17013) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17104 = norm_pat env3 p1 in
                                          (match uu____17104 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16952 with
                           | (pats1,env3) ->
                               ((let uu___365_17186 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___365_17186.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___366_17205 = x in
                            let uu____17206 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___366_17205.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___366_17205.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17206
                            } in
                          ((let uu___367_17220 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___367_17220.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___368_17231 = x in
                            let uu____17232 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___368_17231.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___368_17231.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17232
                            } in
                          ((let uu___369_17246 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___369_17246.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___370_17262 = x in
                            let uu____17263 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___370_17262.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___370_17262.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17263
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___371_17270 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___371_17270.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17280 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17294 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17294 with
                                  | (p,wopt,e) ->
                                      let uu____17314 = norm_pat env1 p in
                                      (match uu____17314 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17339 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17339 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17345 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17345) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17355) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17360 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17361;
                         FStar_Syntax_Syntax.fv_delta = uu____17362;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17363;
                         FStar_Syntax_Syntax.fv_delta = uu____17364;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17365);_}
                       -> true
                   | uu____17372 -> false in
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
                   let uu____17517 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17517 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17604 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17643 ->
                                 let uu____17644 =
                                   let uu____17645 = is_cons head1 in
                                   Prims.op_Negation uu____17645 in
                                 FStar_Util.Inr uu____17644)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17670 =
                              let uu____17671 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17671.FStar_Syntax_Syntax.n in
                            (match uu____17670 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17689 ->
                                 let uu____17690 =
                                   let uu____17691 = is_cons head1 in
                                   Prims.op_Negation uu____17691 in
                                 FStar_Util.Inr uu____17690))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17760)::rest_a,(p1,uu____17763)::rest_p) ->
                       let uu____17807 = matches_pat t1 p1 in
                       (match uu____17807 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17856 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17962 = matches_pat scrutinee1 p1 in
                       (match uu____17962 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18002  ->
                                  let uu____18003 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18004 =
                                    let uu____18005 =
                                      FStar_List.map
                                        (fun uu____18015  ->
                                           match uu____18015 with
                                           | (uu____18020,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18005
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18003 uu____18004);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18051  ->
                                       match uu____18051 with
                                       | (bv,t1) ->
                                           let uu____18074 =
                                             let uu____18081 =
                                               let uu____18084 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18084 in
                                             let uu____18085 =
                                               let uu____18086 =
                                                 let uu____18117 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18117, false) in
                                               Clos uu____18086 in
                                             (uu____18081, uu____18085) in
                                           uu____18074 :: env2) env1 s in
                              let uu____18226 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18226))) in
                 let uu____18227 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18227
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___303_18248  ->
                match uu___303_18248 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18252 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18258 -> d in
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
            let uu___372_18283 = config s e in
            {
              steps = (uu___372_18283.steps);
              tcenv = (uu___372_18283.tcenv);
              delta_level = (uu___372_18283.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___372_18283.strong)
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
      fun t  -> let uu____18308 = config s e in norm_comp uu____18308 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18321 = config [] env in norm_universe uu____18321 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18334 = config [] env in ghost_to_pure_aux uu____18334 [] c
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
        let uu____18352 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18352 in
      let uu____18359 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18359
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___373_18361 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___373_18361.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___373_18361.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18364  ->
                    let uu____18365 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18365))
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
            ((let uu____18382 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18382);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18393 = config [AllowUnboundUniverses] env in
          norm_comp uu____18393 [] c
        with
        | e ->
            ((let uu____18406 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18406);
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
                   let uu____18443 =
                     let uu____18444 =
                       let uu____18451 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18451) in
                     FStar_Syntax_Syntax.Tm_refine uu____18444 in
                   mk uu____18443 t01.FStar_Syntax_Syntax.pos
               | uu____18456 -> t2)
          | uu____18457 -> t2 in
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
        let uu____18497 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18497 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18526 ->
                 let uu____18533 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18533 with
                  | (actuals,uu____18543,uu____18544) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18558 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18558 with
                         | (binders,args) ->
                             let uu____18575 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18575
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
      | uu____18583 ->
          let uu____18584 = FStar_Syntax_Util.head_and_args t in
          (match uu____18584 with
           | (head1,args) ->
               let uu____18621 =
                 let uu____18622 = FStar_Syntax_Subst.compress head1 in
                 uu____18622.FStar_Syntax_Syntax.n in
               (match uu____18621 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18625,thead) ->
                    let uu____18651 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18651 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18693 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___378_18701 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___378_18701.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___378_18701.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___378_18701.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___378_18701.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___378_18701.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___378_18701.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___378_18701.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___378_18701.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___378_18701.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___378_18701.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___378_18701.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___378_18701.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___378_18701.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___378_18701.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___378_18701.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___378_18701.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___378_18701.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___378_18701.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___378_18701.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___378_18701.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___378_18701.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___378_18701.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___378_18701.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___378_18701.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___378_18701.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___378_18701.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___378_18701.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___378_18701.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___378_18701.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___378_18701.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___378_18701.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18693 with
                            | (uu____18702,ty,uu____18704) ->
                                eta_expand_with_type env t ty))
                | uu____18705 ->
                    let uu____18706 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___379_18714 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___379_18714.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___379_18714.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___379_18714.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___379_18714.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___379_18714.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___379_18714.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___379_18714.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___379_18714.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___379_18714.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___379_18714.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___379_18714.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___379_18714.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___379_18714.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___379_18714.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___379_18714.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___379_18714.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___379_18714.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___379_18714.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___379_18714.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___379_18714.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___379_18714.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___379_18714.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___379_18714.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___379_18714.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___379_18714.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___379_18714.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___379_18714.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___379_18714.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___379_18714.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___379_18714.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___379_18714.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18706 with
                     | (uu____18715,ty,uu____18717) ->
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
            | (uu____18791,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18797,FStar_Util.Inl t) ->
                let uu____18803 =
                  let uu____18806 =
                    let uu____18807 =
                      let uu____18820 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18820) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18807 in
                  FStar_Syntax_Syntax.mk uu____18806 in
                uu____18803 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18824 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18824 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18851 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18906 ->
                    let uu____18907 =
                      let uu____18916 =
                        let uu____18917 = FStar_Syntax_Subst.compress t3 in
                        uu____18917.FStar_Syntax_Syntax.n in
                      (uu____18916, tc) in
                    (match uu____18907 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18942) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18979) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19018,FStar_Util.Inl uu____19019) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19042 -> failwith "Impossible") in
              (match uu____18851 with
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
          let uu____19147 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19147 with
          | (univ_names1,binders1,tc) ->
              let uu____19205 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19205)
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
          let uu____19240 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19240 with
          | (univ_names1,binders1,tc) ->
              let uu____19300 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19300)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19333 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19333 with
           | (univ_names1,binders1,typ1) ->
               let uu___380_19361 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___380_19361.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___380_19361.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___380_19361.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___380_19361.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___381_19382 = s in
          let uu____19383 =
            let uu____19384 =
              let uu____19393 = FStar_List.map (elim_uvars env) sigs in
              (uu____19393, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19384 in
          {
            FStar_Syntax_Syntax.sigel = uu____19383;
            FStar_Syntax_Syntax.sigrng =
              (uu___381_19382.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_19382.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_19382.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_19382.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19410 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19410 with
           | (univ_names1,uu____19428,typ1) ->
               let uu___382_19442 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___382_19442.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___382_19442.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___382_19442.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___382_19442.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19448 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19448 with
           | (univ_names1,uu____19466,typ1) ->
               let uu___383_19480 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_19480.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_19480.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_19480.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_19480.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19514 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19514 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19537 =
                            let uu____19538 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19538 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19537 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___384_19541 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___384_19541.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___384_19541.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___385_19542 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___385_19542.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___385_19542.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___385_19542.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___385_19542.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___386_19554 = s in
          let uu____19555 =
            let uu____19556 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19556 in
          {
            FStar_Syntax_Syntax.sigel = uu____19555;
            FStar_Syntax_Syntax.sigrng =
              (uu___386_19554.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___386_19554.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___386_19554.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___386_19554.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19560 = elim_uvars_aux_t env us [] t in
          (match uu____19560 with
           | (us1,uu____19578,t1) ->
               let uu___387_19592 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___387_19592.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___387_19592.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___387_19592.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___387_19592.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19593 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19595 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19595 with
           | (univs1,binders,signature) ->
               let uu____19623 =
                 let uu____19632 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19632 with
                 | (univs_opening,univs2) ->
                     let uu____19659 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19659) in
               (match uu____19623 with
                | (univs_opening,univs_closing) ->
                    let uu____19676 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19682 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19683 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19682, uu____19683) in
                    (match uu____19676 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19705 =
                           match uu____19705 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19723 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19723 with
                                | (us1,t1) ->
                                    let uu____19734 =
                                      let uu____19739 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19746 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19739, uu____19746) in
                                    (match uu____19734 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19759 =
                                           let uu____19764 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19773 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19764, uu____19773) in
                                         (match uu____19759 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19789 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19789 in
                                              let uu____19790 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19790 with
                                               | (uu____19811,uu____19812,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19827 =
                                                       let uu____19828 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19828 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19827 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19833 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19833 with
                           | (uu____19846,uu____19847,t1) -> t1 in
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
                             | uu____19907 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19924 =
                               let uu____19925 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19925.FStar_Syntax_Syntax.n in
                             match uu____19924 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19984 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20013 =
                               let uu____20014 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20014.FStar_Syntax_Syntax.n in
                             match uu____20013 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20035) ->
                                 let uu____20056 = destruct_action_body body in
                                 (match uu____20056 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20101 ->
                                 let uu____20102 = destruct_action_body t in
                                 (match uu____20102 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20151 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20151 with
                           | (action_univs,t) ->
                               let uu____20160 = destruct_action_typ_templ t in
                               (match uu____20160 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___388_20201 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___388_20201.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___388_20201.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___389_20203 = ed in
                           let uu____20204 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20205 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20206 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20207 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20208 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20209 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20210 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20211 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20212 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20213 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20214 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20215 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20216 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20217 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___389_20203.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___389_20203.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20204;
                             FStar_Syntax_Syntax.bind_wp = uu____20205;
                             FStar_Syntax_Syntax.if_then_else = uu____20206;
                             FStar_Syntax_Syntax.ite_wp = uu____20207;
                             FStar_Syntax_Syntax.stronger = uu____20208;
                             FStar_Syntax_Syntax.close_wp = uu____20209;
                             FStar_Syntax_Syntax.assert_p = uu____20210;
                             FStar_Syntax_Syntax.assume_p = uu____20211;
                             FStar_Syntax_Syntax.null_wp = uu____20212;
                             FStar_Syntax_Syntax.trivial = uu____20213;
                             FStar_Syntax_Syntax.repr = uu____20214;
                             FStar_Syntax_Syntax.return_repr = uu____20215;
                             FStar_Syntax_Syntax.bind_repr = uu____20216;
                             FStar_Syntax_Syntax.actions = uu____20217
                           } in
                         let uu___390_20220 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___390_20220.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___390_20220.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___390_20220.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___390_20220.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___304_20237 =
            match uu___304_20237 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20264 = elim_uvars_aux_t env us [] t in
                (match uu____20264 with
                 | (us1,uu____20288,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___391_20307 = sub_eff in
            let uu____20308 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20311 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___391_20307.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___391_20307.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20308;
              FStar_Syntax_Syntax.lift = uu____20311
            } in
          let uu___392_20314 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___392_20314.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___392_20314.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___392_20314.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___392_20314.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20324 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20324 with
           | (univ_names1,binders1,comp1) ->
               let uu___393_20358 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___393_20358.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___393_20358.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___393_20358.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___393_20358.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20369 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t