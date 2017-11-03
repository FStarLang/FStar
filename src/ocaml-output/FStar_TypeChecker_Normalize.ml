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
    let uu____4580 =
      let uu____4583 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4583 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4580 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4613 =
      let uu____4614 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4614 in
    FStar_Syntax_Embeddings.embed_int rng uu____4613 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4632 = arg_as_string a1 in
        (match uu____4632 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4638 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4638 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4651 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4651
              | uu____4652 -> FStar_Pervasives_Native.None)
         | uu____4657 -> FStar_Pervasives_Native.None)
    | uu____4660 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4670 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4670 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4694 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4705 =
          let uu____4726 = arg_as_string fn in
          let uu____4729 = arg_as_int from_line in
          let uu____4732 = arg_as_int from_col in
          let uu____4735 = arg_as_int to_line in
          let uu____4738 = arg_as_int to_col in
          (uu____4726, uu____4729, uu____4732, uu____4735, uu____4738) in
        (match uu____4705 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4769 =
                 let uu____4770 = FStar_BigInt.to_int_fs from_l in
                 let uu____4771 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4770 uu____4771 in
               let uu____4772 =
                 let uu____4773 = FStar_BigInt.to_int_fs to_l in
                 let uu____4774 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4773 uu____4774 in
               FStar_Range.mk_range fn1 uu____4769 uu____4772 in
             let uu____4775 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4775
         | uu____4780 -> FStar_Pervasives_Native.None)
    | uu____4801 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4828)::(a1,uu____4830)::(a2,uu____4832)::[] ->
        let uu____4869 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4869 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4882 -> FStar_Pervasives_Native.None)
    | uu____4883 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4910)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4919 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____4943 =
      let uu____4958 =
        let uu____4973 =
          let uu____4988 =
            let uu____5003 =
              let uu____5018 =
                let uu____5033 =
                  let uu____5048 =
                    let uu____5063 =
                      let uu____5078 =
                        let uu____5093 =
                          let uu____5108 =
                            let uu____5123 =
                              let uu____5138 =
                                let uu____5153 =
                                  let uu____5168 =
                                    let uu____5183 =
                                      let uu____5198 =
                                        let uu____5213 =
                                          let uu____5228 =
                                            let uu____5241 =
                                              FStar_Parser_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____5241,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____5248 =
                                            let uu____5263 =
                                              let uu____5276 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____5276,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list
                                                      FStar_Syntax_Embeddings.unembed_char_safe)
                                                   string_of_list')) in
                                            let uu____5285 =
                                              let uu____5300 =
                                                let uu____5315 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____5315,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              let uu____5324 =
                                                let uu____5341 =
                                                  let uu____5356 =
                                                    FStar_Parser_Const.p2l
                                                      ["Prims"; "mk_range"] in
                                                  (uu____5356,
                                                    (Prims.parse_int "5"),
                                                    mk_range1) in
                                                let uu____5365 =
                                                  let uu____5382 =
                                                    let uu____5401 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "Range";
                                                        "prims_to_fstar_range"] in
                                                    (uu____5401,
                                                      (Prims.parse_int "1"),
                                                      idstep) in
                                                  [uu____5382] in
                                                uu____5341 :: uu____5365 in
                                              uu____5300 :: uu____5324 in
                                            uu____5263 :: uu____5285 in
                                          uu____5228 :: uu____5248 in
                                        (FStar_Parser_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____5213 in
                                      (FStar_Parser_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____5198 in
                                    (FStar_Parser_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____5183 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____5168 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____5153 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5138 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5123 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5108 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5093 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5078 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5737 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5737)))
                      :: uu____5063 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5763 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5763)))
                    :: uu____5048 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5789 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5789)))
                  :: uu____5033 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5815 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5815)))
                :: uu____5018 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5003 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____4988 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____4973 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____4958 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____4943 in
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
      let uu____5965 =
        let uu____5966 =
          let uu____5967 = FStar_Syntax_Syntax.as_arg c in [uu____5967] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5966 in
      uu____5965 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6002 =
              let uu____6015 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6015, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6035  ->
                        fun uu____6036  ->
                          match (uu____6035, uu____6036) with
                          | ((int_to_t1,x),(uu____6055,y)) ->
                              let uu____6065 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6065))) in
            let uu____6066 =
              let uu____6081 =
                let uu____6094 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6094, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6114  ->
                          fun uu____6115  ->
                            match (uu____6114, uu____6115) with
                            | ((int_to_t1,x),(uu____6134,y)) ->
                                let uu____6144 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6144))) in
              let uu____6145 =
                let uu____6160 =
                  let uu____6173 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6173, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6193  ->
                            fun uu____6194  ->
                              match (uu____6193, uu____6194) with
                              | ((int_to_t1,x),(uu____6213,y)) ->
                                  let uu____6223 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6223))) in
                [uu____6160] in
              uu____6081 :: uu____6145 in
            uu____6002 :: uu____6066)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6313)::(a1,uu____6315)::(a2,uu____6317)::[] ->
        let uu____6354 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6354 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___323_6360 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___323_6360.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___323_6360.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___324_6364 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___324_6364.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___324_6364.FStar_Syntax_Syntax.vars)
                })
         | uu____6365 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6367)::uu____6368::(a1,uu____6370)::(a2,uu____6372)::[] ->
        let uu____6421 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6421 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___323_6427 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___323_6427.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___323_6427.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___324_6431 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___324_6431.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___324_6431.FStar_Syntax_Syntax.vars)
                })
         | uu____6432 -> FStar_Pervasives_Native.None)
    | uu____6433 -> failwith "Unexpected number of arguments" in
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
      let uu____6452 =
        let uu____6453 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6453 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6452
    with | uu____6459 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6463 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6463) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6523  ->
           fun subst1  ->
             match uu____6523 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6565)) ->
                      let uu____6624 = b in
                      (match uu____6624 with
                       | (bv,uu____6632) ->
                           let uu____6633 =
                             let uu____6634 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6634 in
                           if uu____6633
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6639 = unembed_binder term1 in
                              match uu____6639 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6646 =
                                      let uu___327_6647 = bv in
                                      let uu____6648 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___327_6647.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___327_6647.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6648
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6646 in
                                  let b_for_x =
                                    let uu____6652 =
                                      let uu____6659 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6659) in
                                    FStar_Syntax_Syntax.NT uu____6652 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___294_6668  ->
                                         match uu___294_6668 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6669,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6671;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6672;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6677 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6678 -> subst1)) env []
let reduce_primops:
  'Auu____6695 'Auu____6696 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6696) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6695 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____6737 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6737
          then tm
          else
            (let uu____6739 = FStar_Syntax_Util.head_and_args tm in
             match uu____6739 with
             | (head1,args) ->
                 let uu____6776 =
                   let uu____6777 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6777.FStar_Syntax_Syntax.n in
                 (match uu____6776 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6781 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6781 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6798  ->
                                   let uu____6799 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6800 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6807 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6799 uu____6800 uu____6807);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6812  ->
                                   let uu____6813 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6813);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6816  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6818 =
                                 prim_step.interpretation psc args in
                               match uu____6818 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6824  ->
                                         let uu____6825 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6825);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6831  ->
                                         let uu____6832 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6833 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6832 uu____6833);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6834 ->
                           (log_primops cfg
                              (fun uu____6838  ->
                                 let uu____6839 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6839);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6843  ->
                            let uu____6844 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6844);
                       (match args with
                        | (a1,uu____6846)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6863 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6875  ->
                            let uu____6876 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6876);
                       (match args with
                        | (a1,uu____6878)::(a2,uu____6880)::[] ->
                            let uu____6907 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____6907 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___328_6911 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___328_6911.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___328_6911.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6914 -> tm))
                  | uu____6923 -> tm))
let reduce_equality:
  'Auu____6928 'Auu____6929 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6929) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6928 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___329_6967 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___329_6967.tcenv);
           delta_level = (uu___329_6967.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___329_6967.strong)
         }) tm
let maybe_simplify:
  'Auu____6974 'Auu____6975 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6975) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6974 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7017 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7017
          then tm1
          else
            (let w t =
               let uu___330_7029 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___330_7029.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___330_7029.FStar_Syntax_Syntax.vars)
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
               | uu____7046 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7086;
                         FStar_Syntax_Syntax.vars = uu____7087;_},uu____7088);
                    FStar_Syntax_Syntax.pos = uu____7089;
                    FStar_Syntax_Syntax.vars = uu____7090;_},args)
                 ->
                 let uu____7116 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7116
                 then
                   let uu____7117 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7117 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7172)::
                        (uu____7173,(arg,uu____7175))::[] -> arg
                    | (uu____7240,(arg,uu____7242))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7243)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7308)::uu____7309::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7372::(FStar_Pervasives_Native.Some (false
                                   ),uu____7373)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7436 -> tm1)
                 else
                   (let uu____7452 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7452
                    then
                      let uu____7453 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7453 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7508)::uu____7509::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7572::(FStar_Pervasives_Native.Some (true
                                     ),uu____7573)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7636)::
                          (uu____7637,(arg,uu____7639))::[] -> arg
                      | (uu____7704,(arg,uu____7706))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7707)::[]
                          -> arg
                      | uu____7772 -> tm1
                    else
                      (let uu____7788 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7788
                       then
                         let uu____7789 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7789 with
                         | uu____7844::(FStar_Pervasives_Native.Some (true
                                        ),uu____7845)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____7908)::uu____7909::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____7972)::
                             (uu____7973,(arg,uu____7975))::[] -> arg
                         | (uu____8040,(p,uu____8042))::(uu____8043,(q,uu____8045))::[]
                             ->
                             let uu____8110 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8110
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8112 -> tm1
                       else
                         (let uu____8128 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8128
                          then
                            let uu____8129 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8129 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8184)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8223)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8262 -> tm1
                          else
                            (let uu____8278 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8278
                             then
                               match args with
                               | (t,uu____8280)::[] ->
                                   let uu____8297 =
                                     let uu____8298 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8298.FStar_Syntax_Syntax.n in
                                   (match uu____8297 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8301::[],body,uu____8303) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8330 -> tm1)
                                    | uu____8333 -> tm1)
                               | (uu____8334,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8335))::
                                   (t,uu____8337)::[] ->
                                   let uu____8376 =
                                     let uu____8377 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8377.FStar_Syntax_Syntax.n in
                                   (match uu____8376 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8380::[],body,uu____8382) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8409 -> tm1)
                                    | uu____8412 -> tm1)
                               | uu____8413 -> tm1
                             else
                               (let uu____8423 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8423
                                then
                                  match args with
                                  | (t,uu____8425)::[] ->
                                      let uu____8442 =
                                        let uu____8443 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8443.FStar_Syntax_Syntax.n in
                                      (match uu____8442 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8446::[],body,uu____8448)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8475 -> tm1)
                                       | uu____8478 -> tm1)
                                  | (uu____8479,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8480))::(t,uu____8482)::[] ->
                                      let uu____8521 =
                                        let uu____8522 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8522.FStar_Syntax_Syntax.n in
                                      (match uu____8521 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8525::[],body,uu____8527)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8554 -> tm1)
                                       | uu____8557 -> tm1)
                                  | uu____8558 -> tm1
                                else
                                  (let uu____8568 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8568
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8569;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8570;_},uu____8571)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8588;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8589;_},uu____8590)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8607 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8618;
                    FStar_Syntax_Syntax.vars = uu____8619;_},args)
                 ->
                 let uu____8641 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8641
                 then
                   let uu____8642 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8642 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8697)::
                        (uu____8698,(arg,uu____8700))::[] -> arg
                    | (uu____8765,(arg,uu____8767))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8768)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8833)::uu____8834::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8897::(FStar_Pervasives_Native.Some (false
                                   ),uu____8898)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8961 -> tm1)
                 else
                   (let uu____8977 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8977
                    then
                      let uu____8978 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8978 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9033)::uu____9034::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9097::(FStar_Pervasives_Native.Some (true
                                     ),uu____9098)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9161)::
                          (uu____9162,(arg,uu____9164))::[] -> arg
                      | (uu____9229,(arg,uu____9231))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9232)::[]
                          -> arg
                      | uu____9297 -> tm1
                    else
                      (let uu____9313 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9313
                       then
                         let uu____9314 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9314 with
                         | uu____9369::(FStar_Pervasives_Native.Some (true
                                        ),uu____9370)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9433)::uu____9434::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9497)::
                             (uu____9498,(arg,uu____9500))::[] -> arg
                         | (uu____9565,(p,uu____9567))::(uu____9568,(q,uu____9570))::[]
                             ->
                             let uu____9635 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9635
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9637 -> tm1
                       else
                         (let uu____9653 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9653
                          then
                            let uu____9654 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9654 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9709)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9748)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9787 -> tm1
                          else
                            (let uu____9803 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9803
                             then
                               match args with
                               | (t,uu____9805)::[] ->
                                   let uu____9822 =
                                     let uu____9823 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9823.FStar_Syntax_Syntax.n in
                                   (match uu____9822 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9826::[],body,uu____9828) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9855 -> tm1)
                                    | uu____9858 -> tm1)
                               | (uu____9859,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9860))::
                                   (t,uu____9862)::[] ->
                                   let uu____9901 =
                                     let uu____9902 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9902.FStar_Syntax_Syntax.n in
                                   (match uu____9901 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9905::[],body,uu____9907) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9934 -> tm1)
                                    | uu____9937 -> tm1)
                               | uu____9938 -> tm1
                             else
                               (let uu____9948 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9948
                                then
                                  match args with
                                  | (t,uu____9950)::[] ->
                                      let uu____9967 =
                                        let uu____9968 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9968.FStar_Syntax_Syntax.n in
                                      (match uu____9967 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9971::[],body,uu____9973)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10000 -> tm1)
                                       | uu____10003 -> tm1)
                                  | (uu____10004,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10005))::(t,uu____10007)::[] ->
                                      let uu____10046 =
                                        let uu____10047 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10047.FStar_Syntax_Syntax.n in
                                      (match uu____10046 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10050::[],body,uu____10052)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10079 -> tm1)
                                       | uu____10082 -> tm1)
                                  | uu____10083 -> tm1
                                else
                                  (let uu____10093 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10093
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10094;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10095;_},uu____10096)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10113;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10114;_},uu____10115)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10132 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | uu____10142 -> tm1)
let is_norm_request:
  'Auu____10146 .
    FStar_Syntax_Syntax.term -> 'Auu____10146 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10159 =
        let uu____10166 =
          let uu____10167 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10167.FStar_Syntax_Syntax.n in
        (uu____10166, args) in
      match uu____10159 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10173::uu____10174::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10178::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10183::uu____10184::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10187 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___295_10198  ->
    match uu___295_10198 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10204 =
          let uu____10207 =
            let uu____10208 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10208 in
          [uu____10207] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10204
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10223 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10223) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10261 =
          let uu____10264 =
            let uu____10269 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10269 s in
          FStar_All.pipe_right uu____10264 FStar_Util.must in
        FStar_All.pipe_right uu____10261 tr_norm_steps in
      match args with
      | uu____10294::(tm,uu____10296)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10319)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10334)::uu____10335::(tm,uu____10337)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10377 =
              let uu____10380 = full_norm steps in parse_steps uu____10380 in
            Beta :: uu____10377 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10389 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___296_10406  ->
    match uu___296_10406 with
    | (App
        (uu____10409,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10410;
                       FStar_Syntax_Syntax.vars = uu____10411;_},uu____10412,uu____10413))::uu____10414
        -> true
    | uu____10421 -> false
let firstn:
  'Auu____10427 .
    Prims.int ->
      'Auu____10427 Prims.list ->
        ('Auu____10427 Prims.list,'Auu____10427 Prims.list)
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
          (uu____10463,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10464;
                         FStar_Syntax_Syntax.vars = uu____10465;_},uu____10466,uu____10467))::uu____10468
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10475 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10591  ->
               let uu____10592 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10593 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10594 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10601 =
                 let uu____10602 =
                   let uu____10605 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10605 in
                 stack_to_string uu____10602 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10592 uu____10593 uu____10594 uu____10601);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10628 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10653 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10670 =
                 let uu____10671 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10672 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10671 uu____10672 in
               failwith uu____10670
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10673 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10690 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10691 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10692;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10693;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10696;
                 FStar_Syntax_Syntax.fv_delta = uu____10697;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10698;
                 FStar_Syntax_Syntax.fv_delta = uu____10699;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10700);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10708 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10708 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10714  ->
                     let uu____10715 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10716 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10715 uu____10716);
                if b
                then
                  (let uu____10717 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10717 t1 fv)
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
                 let uu___331_10756 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___331_10756.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___331_10756.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10789 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10789) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___332_10797 = cfg in
                 let uu____10798 =
                   FStar_List.filter
                     (fun uu___297_10801  ->
                        match uu___297_10801 with
                        | UnfoldOnly uu____10802 -> false
                        | NoDeltaSteps  -> false
                        | uu____10805 -> true) cfg.steps in
                 {
                   steps = uu____10798;
                   tcenv = (uu___332_10797.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___332_10797.primitive_steps);
                   strong = (uu___332_10797.strong)
                 } in
               let uu____10806 = get_norm_request (norm cfg' env []) args in
               (match uu____10806 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10822 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___298_10827  ->
                                match uu___298_10827 with
                                | UnfoldUntil uu____10828 -> true
                                | UnfoldOnly uu____10829 -> true
                                | uu____10832 -> false)) in
                      if uu____10822
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___333_10837 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___333_10837.tcenv);
                        delta_level;
                        primitive_steps = (uu___333_10837.primitive_steps);
                        strong = (uu___333_10837.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10848 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10848
                      then
                        let uu____10851 =
                          let uu____10852 =
                            let uu____10857 = FStar_Util.now () in
                            (t1, uu____10857) in
                          Debug uu____10852 in
                        uu____10851 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____10859;
                  FStar_Syntax_Syntax.vars = uu____10860;_},a1::a2::rest)
               ->
               let uu____10908 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10908 with
                | (hd1,uu____10924) ->
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
                  FStar_Syntax_Syntax.pos = uu____10989;
                  FStar_Syntax_Syntax.vars = uu____10990;_},a1::a2::rest)
               ->
               let uu____11038 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11038 with
                | (hd1,uu____11054) ->
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
                  FStar_Syntax_Syntax.pos = uu____11119;
                  FStar_Syntax_Syntax.vars = uu____11120;_},a1::a2::a3::rest)
               ->
               let uu____11181 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11181 with
                | (hd1,uu____11197) ->
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
                    (FStar_Const.Const_reflect uu____11268);
                  FStar_Syntax_Syntax.pos = uu____11269;
                  FStar_Syntax_Syntax.vars = uu____11270;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11302 = FStar_List.tl stack1 in
               norm cfg env uu____11302 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11305;
                  FStar_Syntax_Syntax.vars = uu____11306;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11338 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11338 with
                | (reify_head,uu____11354) ->
                    let a1 =
                      let uu____11376 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11376 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11379);
                            FStar_Syntax_Syntax.pos = uu____11380;
                            FStar_Syntax_Syntax.vars = uu____11381;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11415 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11425 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11425
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11432 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11432
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11435 =
                      let uu____11442 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11442, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11435 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___299_11455  ->
                         match uu___299_11455 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11458 =
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
                 if uu____11458
                 then false
                 else
                   (let uu____11460 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___300_11467  ->
                              match uu___300_11467 with
                              | UnfoldOnly uu____11468 -> true
                              | uu____11471 -> false)) in
                    match uu____11460 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11475 -> should_delta) in
               (log cfg
                  (fun uu____11483  ->
                     let uu____11484 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11485 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11486 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11484 uu____11485 uu____11486);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11489 = lookup_bvar env x in
               (match uu____11489 with
                | Univ uu____11492 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11541 = FStar_ST.op_Bang r in
                      (match uu____11541 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11678  ->
                                 let uu____11679 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11680 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11679
                                   uu____11680);
                            (let uu____11681 =
                               let uu____11682 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11682.FStar_Syntax_Syntax.n in
                             match uu____11681 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11685 ->
                                 norm cfg env2 stack1 t'
                             | uu____11702 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11760)::uu____11761 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11770)::uu____11771 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11781,uu____11782))::stack_rest ->
                    (match c with
                     | Univ uu____11786 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11795 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11816  ->
                                    let uu____11817 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11817);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11857  ->
                                    let uu____11858 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11858);
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
                      (let uu___334_11908 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___334_11908.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___334_11908.strong)
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11941  ->
                          let uu____11942 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11942);
                     norm cfg env stack2 t1)
                | (Debug uu____11943)::uu____11944 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11951 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11951
                    else
                      (let uu____11953 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11953 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11995  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12023 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12023
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12033 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12033)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12038 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12038.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12038.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12039 -> lopt in
                           (log cfg
                              (fun uu____12045  ->
                                 let uu____12046 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12046);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12059 = cfg in
                               {
                                 steps = (uu___336_12059.steps);
                                 tcenv = (uu___336_12059.tcenv);
                                 delta_level = (uu___336_12059.delta_level);
                                 primitive_steps =
                                   (uu___336_12059.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12070)::uu____12071 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12078 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12078
                    else
                      (let uu____12080 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12080 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12122  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12150 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12150
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12160 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12160)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12165 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12165.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12165.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12166 -> lopt in
                           (log cfg
                              (fun uu____12172  ->
                                 let uu____12173 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12173);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12186 = cfg in
                               {
                                 steps = (uu___336_12186.steps);
                                 tcenv = (uu___336_12186.tcenv);
                                 delta_level = (uu___336_12186.delta_level);
                                 primitive_steps =
                                   (uu___336_12186.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12197)::uu____12198 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12209 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12209
                    else
                      (let uu____12211 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12211 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12253  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12281 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12281
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12291 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12291)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12296 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12296.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12296.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12297 -> lopt in
                           (log cfg
                              (fun uu____12303  ->
                                 let uu____12304 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12304);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12317 = cfg in
                               {
                                 steps = (uu___336_12317.steps);
                                 tcenv = (uu___336_12317.tcenv);
                                 delta_level = (uu___336_12317.delta_level);
                                 primitive_steps =
                                   (uu___336_12317.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12328)::uu____12329 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12340 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12340
                    else
                      (let uu____12342 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12342 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12384  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12412 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12412
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12422 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12422)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12427 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12427.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12427.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12428 -> lopt in
                           (log cfg
                              (fun uu____12434  ->
                                 let uu____12435 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12435);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12448 = cfg in
                               {
                                 steps = (uu___336_12448.steps);
                                 tcenv = (uu___336_12448.tcenv);
                                 delta_level = (uu___336_12448.delta_level);
                                 primitive_steps =
                                   (uu___336_12448.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12459)::uu____12460 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12475 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12475
                    else
                      (let uu____12477 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12477 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12519  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12547 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12547
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12557 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12557)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12562 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12562.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12562.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12563 -> lopt in
                           (log cfg
                              (fun uu____12569  ->
                                 let uu____12570 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12570);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12583 = cfg in
                               {
                                 steps = (uu___336_12583.steps);
                                 tcenv = (uu___336_12583.tcenv);
                                 delta_level = (uu___336_12583.delta_level);
                                 primitive_steps =
                                   (uu___336_12583.primitive_steps);
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
                      let uu____12594 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12594
                    else
                      (let uu____12596 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12596 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12638  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12666 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12666
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12676 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12676)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___335_12681 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___335_12681.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___335_12681.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12682 -> lopt in
                           (log cfg
                              (fun uu____12688  ->
                                 let uu____12689 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12689);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___336_12702 = cfg in
                               {
                                 steps = (uu___336_12702.steps);
                                 tcenv = (uu___336_12702.tcenv);
                                 delta_level = (uu___336_12702.delta_level);
                                 primitive_steps =
                                   (uu___336_12702.primitive_steps);
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
                      (fun uu____12751  ->
                         fun stack2  ->
                           match uu____12751 with
                           | (a,aq) ->
                               let uu____12763 =
                                 let uu____12764 =
                                   let uu____12771 =
                                     let uu____12772 =
                                       let uu____12803 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12803, false) in
                                     Clos uu____12772 in
                                   (uu____12771, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12764 in
                               uu____12763 :: stack2) args) in
               (log cfg
                  (fun uu____12879  ->
                     let uu____12880 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12880);
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
                             ((let uu___337_12916 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___337_12916.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___337_12916.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12917 ->
                      let uu____12922 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12922)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12925 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12925 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12956 =
                          let uu____12957 =
                            let uu____12964 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___338_12966 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___338_12966.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___338_12966.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12964) in
                          FStar_Syntax_Syntax.Tm_refine uu____12957 in
                        mk uu____12956 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12985 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12985
               else
                 (let uu____12987 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12987 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12995 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13019  -> dummy :: env1) env) in
                        norm_comp cfg uu____12995 c1 in
                      let t2 =
                        let uu____13041 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13041 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13100)::uu____13101 ->
                    (log cfg
                       (fun uu____13112  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13113)::uu____13114 ->
                    (log cfg
                       (fun uu____13125  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13126,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13127;
                                   FStar_Syntax_Syntax.vars = uu____13128;_},uu____13129,uu____13130))::uu____13131
                    ->
                    (log cfg
                       (fun uu____13140  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13141)::uu____13142 ->
                    (log cfg
                       (fun uu____13153  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13154 ->
                    (log cfg
                       (fun uu____13157  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13161  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13178 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13178
                         | FStar_Util.Inr c ->
                             let uu____13186 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13186 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13192 =
                         let uu____13193 =
                           let uu____13194 =
                             let uu____13221 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13221, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13194 in
                         mk uu____13193 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13192))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13297,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13298;
                               FStar_Syntax_Syntax.lbunivs = uu____13299;
                               FStar_Syntax_Syntax.lbtyp = uu____13300;
                               FStar_Syntax_Syntax.lbeff = uu____13301;
                               FStar_Syntax_Syntax.lbdef = uu____13302;_}::uu____13303),uu____13304)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13340 =
                 (let uu____13343 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13343) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13345 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13345))) in
               if uu____13340
               then
                 let binder =
                   let uu____13347 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13347 in
                 let env1 =
                   let uu____13357 =
                     let uu____13364 =
                       let uu____13365 =
                         let uu____13396 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13396,
                           false) in
                       Clos uu____13365 in
                     ((FStar_Pervasives_Native.Some binder), uu____13364) in
                   uu____13357 :: env in
                 (log cfg
                    (fun uu____13481  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13483 =
                    let uu____13488 =
                      let uu____13489 =
                        let uu____13490 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13490
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13489] in
                    FStar_Syntax_Subst.open_term uu____13488 body in
                  match uu____13483 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13499  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13507 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13507 in
                          FStar_Util.Inl
                            (let uu___339_13517 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___339_13517.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___339_13517.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13520  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___340_13522 = lb in
                           let uu____13523 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___340_13522.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___340_13522.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13523
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13558  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___341_13578 = cfg in
                           {
                             steps = (uu___341_13578.steps);
                             tcenv = (uu___341_13578.tcenv);
                             delta_level = (uu___341_13578.delta_level);
                             primitive_steps =
                               (uu___341_13578.primitive_steps);
                             strong = true
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
                               let uu___342_13635 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___342_13635.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___342_13635.FStar_Syntax_Syntax.index);
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
                                       let uu___343_13733 = rc in
                                       let uu____13734 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___343_13733.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13734;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___343_13733.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13732
                                 | uu____13741 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___344_13745 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___344_13745.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___344_13745.FStar_Syntax_Syntax.lbeff);
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
                           let uu___345_13795 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___345_13795.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___345_13795.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13822 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13822
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13841 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13917  ->
                        match uu____13917 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___346_14038 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___346_14038.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___346_14038.FStar_Syntax_Syntax.sort)
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
                | (rec_env,memos,uu____14235) ->
                    let uu____14288 =
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
                             let uu____14819 =
                               let uu____14826 =
                                 let uu____14827 =
                                   let uu____14858 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14858, false) in
                                 Clos uu____14827 in
                               (FStar_Pervasives_Native.None, uu____14826) in
                             uu____14819 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14963 =
                      let uu____14964 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14964 in
                    if uu____14963
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14974 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14974
                        then
                          let uu___347_14975 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___347_14975.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___347_14975.primitive_steps);
                            strong = (uu___347_14975.strong)
                          }
                        else
                          (let uu___348_14977 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___348_14977.tcenv);
                             delta_level = (uu___348_14977.delta_level);
                             primitive_steps =
                               (uu___348_14977.primitive_steps);
                             strong = (uu___348_14977.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14979 =
                         let uu____14980 = FStar_Syntax_Subst.compress head1 in
                         uu____14980.FStar_Syntax_Syntax.n in
                       match uu____14979 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14998 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14998 with
                            | (uu____14999,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15005 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15013 =
                                         let uu____15014 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15014.FStar_Syntax_Syntax.n in
                                       match uu____15013 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15020,uu____15021))
                                           ->
                                           let uu____15030 =
                                             let uu____15031 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15031.FStar_Syntax_Syntax.n in
                                           (match uu____15030 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15037,msrc,uu____15039))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15048 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15048
                                            | uu____15049 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15050 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15051 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15051 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___349_15056 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___349_15056.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___349_15056.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___349_15056.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15057 =
                                            FStar_List.tl stack1 in
                                          let uu____15058 =
                                            let uu____15059 =
                                              let uu____15062 =
                                                let uu____15063 =
                                                  let uu____15076 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15076) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15063 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15062 in
                                            uu____15059
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15057
                                            uu____15058
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15092 =
                                            let uu____15093 = is_return body in
                                            match uu____15093 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15097;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15098;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15103 -> false in
                                          if uu____15092
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
                                               let uu____15127 =
                                                 let uu____15130 =
                                                   let uu____15131 =
                                                     let uu____15148 =
                                                       let uu____15151 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15151] in
                                                     (uu____15148, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15131 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15130 in
                                               uu____15127
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15167 =
                                                 let uu____15168 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15168.FStar_Syntax_Syntax.n in
                                               match uu____15167 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15174::uu____15175::[])
                                                   ->
                                                   let uu____15182 =
                                                     let uu____15185 =
                                                       let uu____15186 =
                                                         let uu____15193 =
                                                           let uu____15196 =
                                                             let uu____15197
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15197 in
                                                           let uu____15198 =
                                                             let uu____15201
                                                               =
                                                               let uu____15202
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15202 in
                                                             [uu____15201] in
                                                           uu____15196 ::
                                                             uu____15198 in
                                                         (bind1, uu____15193) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15186 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15185 in
                                                   uu____15182
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15210 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15216 =
                                                 let uu____15219 =
                                                   let uu____15220 =
                                                     let uu____15235 =
                                                       let uu____15238 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15239 =
                                                         let uu____15242 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15243 =
                                                           let uu____15246 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15247 =
                                                             let uu____15250
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15251
                                                               =
                                                               let uu____15254
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15255
                                                                 =
                                                                 let uu____15258
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15258] in
                                                               uu____15254 ::
                                                                 uu____15255 in
                                                             uu____15250 ::
                                                               uu____15251 in
                                                           uu____15246 ::
                                                             uu____15247 in
                                                         uu____15242 ::
                                                           uu____15243 in
                                                       uu____15238 ::
                                                         uu____15239 in
                                                     (bind_inst, uu____15235) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15220 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15219 in
                                               uu____15216
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15266 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15266 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15290 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15290 with
                            | (uu____15291,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15326 =
                                        let uu____15327 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15327.FStar_Syntax_Syntax.n in
                                      match uu____15326 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15333) -> t4
                                      | uu____15338 -> head2 in
                                    let uu____15339 =
                                      let uu____15340 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15340.FStar_Syntax_Syntax.n in
                                    match uu____15339 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15346 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15347 = maybe_extract_fv head2 in
                                  match uu____15347 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15357 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15357
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15362 =
                                          maybe_extract_fv head3 in
                                        match uu____15362 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15367 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15368 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15373 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15388 =
                                    match uu____15388 with
                                    | (e,q) ->
                                        let uu____15395 =
                                          let uu____15396 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15396.FStar_Syntax_Syntax.n in
                                        (match uu____15395 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15411 -> false) in
                                  let uu____15412 =
                                    let uu____15413 =
                                      let uu____15420 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15420 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15413 in
                                  if uu____15412
                                  then
                                    let uu____15425 =
                                      let uu____15426 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15426 in
                                    failwith uu____15425
                                  else ());
                                 (let uu____15428 =
                                    maybe_unfold_action head_app in
                                  match uu____15428 with
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
                                      let uu____15467 = FStar_List.tl stack1 in
                                      norm cfg env uu____15467 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15481 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15481 in
                           let uu____15482 = FStar_List.tl stack1 in
                           norm cfg env uu____15482 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15603  ->
                                     match uu____15603 with
                                     | (pat,wopt,tm) ->
                                         let uu____15651 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15651))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15683 = FStar_List.tl stack1 in
                           norm cfg env uu____15683 tm
                       | uu____15684 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15692 = should_reify cfg stack1 in
                    if uu____15692
                    then
                      let uu____15693 = FStar_List.tl stack1 in
                      let uu____15694 =
                        let uu____15695 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15695 in
                      norm cfg env uu____15693 uu____15694
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15698 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15698
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___350_15707 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___350_15707.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___350_15707.primitive_steps);
                             strong = (uu___350_15707.strong)
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
                | uu____15709 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15711::uu____15712 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15717) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15718 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15749 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15763 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15763
                             | uu____15774 -> m in
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
              let uu____15786 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15786 in
            let uu____15787 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15787 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15800  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15811  ->
                      let uu____15812 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15813 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15812
                        uu____15813);
                 (let t1 =
                    let uu____15815 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15815
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
                    | (UnivArgs (us',uu____15825))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____15880 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15883 ->
                        let uu____15886 =
                          let uu____15887 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15887 in
                        failwith uu____15886
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
              let uu____15897 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15897 with
              | (uu____15898,return_repr) ->
                  let return_inst =
                    let uu____15907 =
                      let uu____15908 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15908.FStar_Syntax_Syntax.n in
                    match uu____15907 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15914::[]) ->
                        let uu____15921 =
                          let uu____15924 =
                            let uu____15925 =
                              let uu____15932 =
                                let uu____15935 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15935] in
                              (return_tm, uu____15932) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15925 in
                          FStar_Syntax_Syntax.mk uu____15924 in
                        uu____15921 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15943 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15946 =
                    let uu____15949 =
                      let uu____15950 =
                        let uu____15965 =
                          let uu____15968 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15969 =
                            let uu____15972 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15972] in
                          uu____15968 :: uu____15969 in
                        (return_inst, uu____15965) in
                      FStar_Syntax_Syntax.Tm_app uu____15950 in
                    FStar_Syntax_Syntax.mk uu____15949 in
                  uu____15946 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15981 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15981 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15984 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15984
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15985;
                     FStar_TypeChecker_Env.mtarget = uu____15986;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15987;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15998;
                     FStar_TypeChecker_Env.mtarget = uu____15999;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16000;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16018 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16018)
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
                (fun uu____16074  ->
                   match uu____16074 with
                   | (a,imp) ->
                       let uu____16085 = norm cfg env [] a in
                       (uu____16085, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___351_16102 = comp1 in
            let uu____16105 =
              let uu____16106 =
                let uu____16115 = norm cfg env [] t in
                let uu____16116 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16115, uu____16116) in
              FStar_Syntax_Syntax.Total uu____16106 in
            {
              FStar_Syntax_Syntax.n = uu____16105;
              FStar_Syntax_Syntax.pos =
                (uu___351_16102.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___351_16102.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___352_16131 = comp1 in
            let uu____16134 =
              let uu____16135 =
                let uu____16144 = norm cfg env [] t in
                let uu____16145 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16144, uu____16145) in
              FStar_Syntax_Syntax.GTotal uu____16135 in
            {
              FStar_Syntax_Syntax.n = uu____16134;
              FStar_Syntax_Syntax.pos =
                (uu___352_16131.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___352_16131.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16197  ->
                      match uu____16197 with
                      | (a,i) ->
                          let uu____16208 = norm cfg env [] a in
                          (uu____16208, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___301_16219  ->
                      match uu___301_16219 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16223 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16223
                      | f -> f)) in
            let uu___353_16227 = comp1 in
            let uu____16230 =
              let uu____16231 =
                let uu___354_16232 = ct in
                let uu____16233 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16234 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16237 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16233;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___354_16232.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16234;
                  FStar_Syntax_Syntax.effect_args = uu____16237;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16231 in
            {
              FStar_Syntax_Syntax.n = uu____16230;
              FStar_Syntax_Syntax.pos =
                (uu___353_16227.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___353_16227.FStar_Syntax_Syntax.vars)
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
            (let uu___355_16255 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___355_16255.tcenv);
               delta_level = (uu___355_16255.delta_level);
               primitive_steps = (uu___355_16255.primitive_steps);
               strong = (uu___355_16255.strong)
             }) env [] t in
        let non_info t =
          let uu____16260 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16260 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16263 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___356_16282 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___356_16282.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___356_16282.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16289 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16289
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
                    let uu___357_16300 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___357_16300.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___357_16300.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___357_16300.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___358_16302 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___358_16302.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___358_16302.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___358_16302.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___358_16302.FStar_Syntax_Syntax.flags)
                    } in
              let uu___359_16303 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___359_16303.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___359_16303.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16305 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16308  ->
        match uu____16308 with
        | (x,imp) ->
            let uu____16311 =
              let uu___360_16312 = x in
              let uu____16313 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___360_16312.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___360_16312.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16313
              } in
            (uu____16311, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16319 =
          FStar_List.fold_left
            (fun uu____16337  ->
               fun b  ->
                 match uu____16337 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16319 with | (nbs,uu____16377) -> FStar_List.rev nbs
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
            let uu____16393 =
              let uu___361_16394 = rc in
              let uu____16395 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___361_16394.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16395;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___361_16394.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16393
        | uu____16402 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16415  ->
               let uu____16416 = FStar_Syntax_Print.tag_of_term t in
               let uu____16417 = FStar_Syntax_Print.term_to_string t in
               let uu____16418 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16425 =
                 let uu____16426 =
                   let uu____16429 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16429 in
                 stack_to_string uu____16426 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16416 uu____16417 uu____16418 uu____16425);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16458 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16458
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16460 =
                     let uu____16461 =
                       let uu____16462 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16462 in
                     FStar_Util.string_of_int uu____16461 in
                   let uu____16467 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16468 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16460 uu____16467 uu____16468
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___362_16486 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___362_16486.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___362_16486.strong)
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16527  ->
                     let uu____16528 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16528);
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
               let uu____16564 =
                 let uu___363_16565 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___363_16565.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___363_16565.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16564
           | (Arg (Univ uu____16566,uu____16567,uu____16568))::uu____16569 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16572,uu____16573))::uu____16574 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16590),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16643  ->
                     let uu____16644 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16644);
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
                  (let uu____16654 = FStar_ST.op_Bang m in
                   match uu____16654 with
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
                   | FStar_Pervasives_Native.Some (uu____16798,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16841 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16841
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16853  ->
                     let uu____16854 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16854);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16859 =
                   log cfg
                     (fun uu____16864  ->
                        let uu____16865 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16866 =
                          let uu____16867 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16884  ->
                                    match uu____16884 with
                                    | (p,uu____16894,uu____16895) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16867
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16865 uu____16866);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___302_16912  ->
                                match uu___302_16912 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16913 -> false)) in
                      let steps' =
                        let uu____16917 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____16917
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      let uu___364_16921 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___364_16921.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___364_16921.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16953 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16974 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17034  ->
                                    fun uu____17035  ->
                                      match (uu____17034, uu____17035) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17126 = norm_pat env3 p1 in
                                          (match uu____17126 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16974 with
                           | (pats1,env3) ->
                               ((let uu___365_17208 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___365_17208.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___366_17227 = x in
                            let uu____17228 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___366_17227.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___366_17227.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17228
                            } in
                          ((let uu___367_17242 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___367_17242.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___368_17253 = x in
                            let uu____17254 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___368_17253.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___368_17253.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17254
                            } in
                          ((let uu___369_17268 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___369_17268.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___370_17284 = x in
                            let uu____17285 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___370_17284.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___370_17284.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17285
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___371_17292 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___371_17292.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17302 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17316 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17316 with
                                  | (p,wopt,e) ->
                                      let uu____17336 = norm_pat env1 p in
                                      (match uu____17336 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17361 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17361 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17367 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17367) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17377) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17382 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17383;
                         FStar_Syntax_Syntax.fv_delta = uu____17384;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17385;
                         FStar_Syntax_Syntax.fv_delta = uu____17386;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17387);_}
                       -> true
                   | uu____17394 -> false in
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
                   let uu____17539 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17539 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17626 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____17665 ->
                                 let uu____17666 =
                                   let uu____17667 = is_cons head1 in
                                   Prims.op_Negation uu____17667 in
                                 FStar_Util.Inr uu____17666)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17692 =
                              let uu____17693 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17693.FStar_Syntax_Syntax.n in
                            (match uu____17692 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17711 ->
                                 let uu____17712 =
                                   let uu____17713 = is_cons head1 in
                                   Prims.op_Negation uu____17713 in
                                 FStar_Util.Inr uu____17712))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17782)::rest_a,(p1,uu____17785)::rest_p) ->
                       let uu____17829 = matches_pat t1 p1 in
                       (match uu____17829 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17878 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17984 = matches_pat scrutinee1 p1 in
                       (match uu____17984 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18024  ->
                                  let uu____18025 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18026 =
                                    let uu____18027 =
                                      FStar_List.map
                                        (fun uu____18037  ->
                                           match uu____18037 with
                                           | (uu____18042,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18027
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18025 uu____18026);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18073  ->
                                       match uu____18073 with
                                       | (bv,t1) ->
                                           let uu____18096 =
                                             let uu____18103 =
                                               let uu____18106 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18106 in
                                             let uu____18107 =
                                               let uu____18108 =
                                                 let uu____18139 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18139, false) in
                                               Clos uu____18108 in
                                             (uu____18103, uu____18107) in
                                           uu____18096 :: env2) env1 s in
                              let uu____18248 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18248))) in
                 let uu____18249 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18249
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___303_18270  ->
                match uu___303_18270 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18274 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18280 -> d in
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
            let uu___372_18305 = config s e in
            {
              steps = (uu___372_18305.steps);
              tcenv = (uu___372_18305.tcenv);
              delta_level = (uu___372_18305.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___372_18305.strong)
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
      fun t  -> let uu____18330 = config s e in norm_comp uu____18330 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18343 = config [] env in norm_universe uu____18343 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18356 = config [] env in ghost_to_pure_aux uu____18356 [] c
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
        let uu____18374 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18374 in
      let uu____18381 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18381
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___373_18383 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___373_18383.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___373_18383.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18386  ->
                    let uu____18387 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18387))
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
            ((let uu____18404 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18404);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18415 = config [AllowUnboundUniverses] env in
          norm_comp uu____18415 [] c
        with
        | e ->
            ((let uu____18428 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18428);
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
                   let uu____18465 =
                     let uu____18466 =
                       let uu____18473 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18473) in
                     FStar_Syntax_Syntax.Tm_refine uu____18466 in
                   mk uu____18465 t01.FStar_Syntax_Syntax.pos
               | uu____18478 -> t2)
          | uu____18479 -> t2 in
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
        let uu____18519 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18519 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18548 ->
                 let uu____18555 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18555 with
                  | (actuals,uu____18565,uu____18566) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18580 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18580 with
                         | (binders,args) ->
                             let uu____18597 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18597
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
      | uu____18605 ->
          let uu____18606 = FStar_Syntax_Util.head_and_args t in
          (match uu____18606 with
           | (head1,args) ->
               let uu____18643 =
                 let uu____18644 = FStar_Syntax_Subst.compress head1 in
                 uu____18644.FStar_Syntax_Syntax.n in
               (match uu____18643 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18647,thead) ->
                    let uu____18673 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18673 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18715 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___378_18723 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___378_18723.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___378_18723.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___378_18723.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___378_18723.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___378_18723.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___378_18723.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___378_18723.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___378_18723.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___378_18723.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___378_18723.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___378_18723.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___378_18723.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___378_18723.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___378_18723.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___378_18723.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___378_18723.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___378_18723.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___378_18723.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___378_18723.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___378_18723.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___378_18723.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___378_18723.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___378_18723.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___378_18723.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___378_18723.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___378_18723.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___378_18723.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___378_18723.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___378_18723.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___378_18723.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___378_18723.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18715 with
                            | (uu____18724,ty,uu____18726) ->
                                eta_expand_with_type env t ty))
                | uu____18727 ->
                    let uu____18728 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___379_18736 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___379_18736.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___379_18736.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___379_18736.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___379_18736.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___379_18736.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___379_18736.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___379_18736.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___379_18736.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___379_18736.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___379_18736.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___379_18736.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___379_18736.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___379_18736.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___379_18736.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___379_18736.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___379_18736.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___379_18736.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___379_18736.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___379_18736.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___379_18736.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___379_18736.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___379_18736.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___379_18736.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___379_18736.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___379_18736.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___379_18736.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___379_18736.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___379_18736.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___379_18736.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___379_18736.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___379_18736.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18728 with
                     | (uu____18737,ty,uu____18739) ->
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
            | (uu____18813,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18819,FStar_Util.Inl t) ->
                let uu____18825 =
                  let uu____18828 =
                    let uu____18829 =
                      let uu____18842 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18842) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18829 in
                  FStar_Syntax_Syntax.mk uu____18828 in
                uu____18825 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18846 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18846 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18873 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18928 ->
                    let uu____18929 =
                      let uu____18938 =
                        let uu____18939 = FStar_Syntax_Subst.compress t3 in
                        uu____18939.FStar_Syntax_Syntax.n in
                      (uu____18938, tc) in
                    (match uu____18929 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18964) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19001) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19040,FStar_Util.Inl uu____19041) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19064 -> failwith "Impossible") in
              (match uu____18873 with
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
          let uu____19169 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19169 with
          | (univ_names1,binders1,tc) ->
              let uu____19227 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19227)
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
          let uu____19262 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19262 with
          | (univ_names1,binders1,tc) ->
              let uu____19322 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19322)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19355 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19355 with
           | (univ_names1,binders1,typ1) ->
               let uu___380_19383 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___380_19383.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___380_19383.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___380_19383.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___380_19383.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___381_19404 = s in
          let uu____19405 =
            let uu____19406 =
              let uu____19415 = FStar_List.map (elim_uvars env) sigs in
              (uu____19415, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19406 in
          {
            FStar_Syntax_Syntax.sigel = uu____19405;
            FStar_Syntax_Syntax.sigrng =
              (uu___381_19404.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_19404.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_19404.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_19404.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19432 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19432 with
           | (univ_names1,uu____19450,typ1) ->
               let uu___382_19464 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___382_19464.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___382_19464.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___382_19464.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___382_19464.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19470 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19470 with
           | (univ_names1,uu____19488,typ1) ->
               let uu___383_19502 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_19502.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_19502.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_19502.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_19502.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19536 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19536 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19559 =
                            let uu____19560 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19560 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19559 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___384_19563 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___384_19563.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___384_19563.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___385_19564 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___385_19564.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___385_19564.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___385_19564.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___385_19564.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___386_19576 = s in
          let uu____19577 =
            let uu____19578 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19578 in
          {
            FStar_Syntax_Syntax.sigel = uu____19577;
            FStar_Syntax_Syntax.sigrng =
              (uu___386_19576.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___386_19576.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___386_19576.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___386_19576.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19582 = elim_uvars_aux_t env us [] t in
          (match uu____19582 with
           | (us1,uu____19600,t1) ->
               let uu___387_19614 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___387_19614.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___387_19614.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___387_19614.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___387_19614.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19615 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19617 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19617 with
           | (univs1,binders,signature) ->
               let uu____19645 =
                 let uu____19654 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19654 with
                 | (univs_opening,univs2) ->
                     let uu____19681 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19681) in
               (match uu____19645 with
                | (univs_opening,univs_closing) ->
                    let uu____19698 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19704 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19705 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19704, uu____19705) in
                    (match uu____19698 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19727 =
                           match uu____19727 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19745 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19745 with
                                | (us1,t1) ->
                                    let uu____19756 =
                                      let uu____19761 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19768 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19761, uu____19768) in
                                    (match uu____19756 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19781 =
                                           let uu____19786 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19795 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19786, uu____19795) in
                                         (match uu____19781 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19811 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19811 in
                                              let uu____19812 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19812 with
                                               | (uu____19833,uu____19834,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19849 =
                                                       let uu____19850 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19850 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19849 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19855 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19855 with
                           | (uu____19868,uu____19869,t1) -> t1 in
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
                             | uu____19929 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19946 =
                               let uu____19947 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19947.FStar_Syntax_Syntax.n in
                             match uu____19946 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20006 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20035 =
                               let uu____20036 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20036.FStar_Syntax_Syntax.n in
                             match uu____20035 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20057) ->
                                 let uu____20078 = destruct_action_body body in
                                 (match uu____20078 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20123 ->
                                 let uu____20124 = destruct_action_body t in
                                 (match uu____20124 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20173 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20173 with
                           | (action_univs,t) ->
                               let uu____20182 = destruct_action_typ_templ t in
                               (match uu____20182 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___388_20223 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___388_20223.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___388_20223.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___389_20225 = ed in
                           let uu____20226 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20227 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20228 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20229 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20230 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20231 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20232 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20233 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20234 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20235 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20236 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20237 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20238 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20239 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___389_20225.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___389_20225.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20226;
                             FStar_Syntax_Syntax.bind_wp = uu____20227;
                             FStar_Syntax_Syntax.if_then_else = uu____20228;
                             FStar_Syntax_Syntax.ite_wp = uu____20229;
                             FStar_Syntax_Syntax.stronger = uu____20230;
                             FStar_Syntax_Syntax.close_wp = uu____20231;
                             FStar_Syntax_Syntax.assert_p = uu____20232;
                             FStar_Syntax_Syntax.assume_p = uu____20233;
                             FStar_Syntax_Syntax.null_wp = uu____20234;
                             FStar_Syntax_Syntax.trivial = uu____20235;
                             FStar_Syntax_Syntax.repr = uu____20236;
                             FStar_Syntax_Syntax.return_repr = uu____20237;
                             FStar_Syntax_Syntax.bind_repr = uu____20238;
                             FStar_Syntax_Syntax.actions = uu____20239
                           } in
                         let uu___390_20242 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___390_20242.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___390_20242.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___390_20242.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___390_20242.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___304_20259 =
            match uu___304_20259 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20286 = elim_uvars_aux_t env us [] t in
                (match uu____20286 with
                 | (us1,uu____20310,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___391_20329 = sub_eff in
            let uu____20330 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20333 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___391_20329.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___391_20329.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20330;
              FStar_Syntax_Syntax.lift = uu____20333
            } in
          let uu___392_20336 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___392_20336.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___392_20336.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___392_20336.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___392_20336.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20346 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20346 with
           | (univ_names1,binders1,comp1) ->
               let uu___393_20380 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___393_20380.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___393_20380.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___393_20380.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___393_20380.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20391 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t