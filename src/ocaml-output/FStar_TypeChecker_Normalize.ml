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
  fun uu___188_497  ->
    match uu___188_497 with
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
  fun uu___189_1392  ->
    match uu___189_1392 with
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
  fun uu___190_1508  ->
    match uu___190_1508 with | [] -> true | uu____1511 -> false
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
                           (let uu___209_2733 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___209_2733.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___209_2733.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2721)) in
                  (match uu____2691 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___210_2749 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___210_2749.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___210_2749.FStar_Syntax_Syntax.lbeff);
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
                           (let uu___211_2898 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___211_2898.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___211_2898.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___212_2899 = lb in
                    let uu____2900 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___212_2899.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___212_2899.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___213_3329 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___213_3329.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___214_3348 = x in
                                let uu____3349 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___214_3348.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___214_3348.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3349
                                } in
                              ((let uu___215_3363 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___215_3363.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___216_3374 = x in
                                let uu____3375 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___216_3374.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___216_3374.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3375
                                } in
                              ((let uu___217_3389 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___217_3389.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___218_3405 = x in
                                let uu____3406 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___218_3405.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___218_3405.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3406
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___219_3413 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___219_3413.FStar_Syntax_Syntax.p)
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
                          let uu___220_3757 = b in
                          let uu____3758 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___220_3757.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___220_3757.FStar_Syntax_Syntax.index);
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
                        (fun uu___191_3905  ->
                           match uu___191_3905 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3909 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3909
                           | f -> f)) in
                 let uu____3913 =
                   let uu___221_3914 = c1 in
                   let uu____3915 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3915;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___221_3914.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___192_3925  ->
            match uu___192_3925 with
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
                   (fun uu___193_3947  ->
                      match uu___193_3947 with
                      | FStar_Syntax_Syntax.DECREASES uu____3948 -> false
                      | uu____3951 -> true)) in
            let rc1 =
              let uu___222_3953 = rc in
              let uu____3954 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___222_3953.FStar_Syntax_Syntax.residual_effect);
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
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4656 =
          let uu____4665 = as_a a in
          let uu____4668 = as_b b in (uu____4665, uu____4668) in
        (match uu____4656 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4683 =
               let uu____4684 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4684 in
             FStar_Pervasives_Native.Some uu____4683
         | uu____4685 -> FStar_Pervasives_Native.None)
    | uu____4694 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4708 =
        let uu____4709 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4709 in
      mk uu____4708 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4719 =
      let uu____4722 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4722 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4719 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4754 =
      let uu____4755 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4755 in
    FStar_Syntax_Embeddings.embed_int rng uu____4754 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4773 = arg_as_string a1 in
        (match uu____4773 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4779 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4779 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4792 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4792
              | uu____4793 -> FStar_Pervasives_Native.None)
         | uu____4798 -> FStar_Pervasives_Native.None)
    | uu____4801 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4811 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4811 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4835 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4846 =
          let uu____4867 = arg_as_string fn in
          let uu____4870 = arg_as_int from_line in
          let uu____4873 = arg_as_int from_col in
          let uu____4876 = arg_as_int to_line in
          let uu____4879 = arg_as_int to_col in
          (uu____4867, uu____4870, uu____4873, uu____4876, uu____4879) in
        (match uu____4846 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4910 =
                 let uu____4911 = FStar_BigInt.to_int_fs from_l in
                 let uu____4912 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4911 uu____4912 in
               let uu____4913 =
                 let uu____4914 = FStar_BigInt.to_int_fs to_l in
                 let uu____4915 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4914 uu____4915 in
               FStar_Range.mk_range fn1 uu____4910 uu____4913 in
             let uu____4916 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4916
         | uu____4921 -> FStar_Pervasives_Native.None)
    | uu____4942 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4969)::(a1,uu____4971)::(a2,uu____4973)::[] ->
        let uu____5010 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5010 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5023 -> FStar_Pervasives_Native.None)
    | uu____5024 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5051)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5060 -> failwith "Unexpected number of arguments" in
  let basic_ops =
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
                                          let uu____5369 =
                                            let uu____5384 =
                                              let uu____5397 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5397,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5404 =
                                              let uu____5419 =
                                                let uu____5432 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5432,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5443 =
                                                let uu____5458 =
                                                  let uu____5473 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5473,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5482 =
                                                  let uu____5499 =
                                                    let uu____5514 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5514,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5523 =
                                                    let uu____5540 =
                                                      let uu____5559 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5559,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5540] in
                                                  uu____5499 :: uu____5523 in
                                                uu____5458 :: uu____5482 in
                                              uu____5419 :: uu____5443 in
                                            uu____5384 :: uu____5404 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5369 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5354 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5339 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5324 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5309 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5777 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5777 y)))
                                  :: uu____5294 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5279 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5264 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5249 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5234 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5219 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5923 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5923)))
                      :: uu____5204 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5949 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5949)))
                    :: uu____5189 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5975 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5975)))
                  :: uu____5174 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____6001 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____6001)))
                :: uu____5159 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5144 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5129 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5114 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5099 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5084 in
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
      let uu____6151 =
        let uu____6152 =
          let uu____6153 = FStar_Syntax_Syntax.as_arg c in [uu____6153] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6152 in
      uu____6151 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6188 =
              let uu____6201 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6201, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6221  ->
                        fun uu____6222  ->
                          match (uu____6221, uu____6222) with
                          | ((int_to_t1,x),(uu____6241,y)) ->
                              let uu____6251 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6251))) in
            let uu____6252 =
              let uu____6267 =
                let uu____6280 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6280, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6300  ->
                          fun uu____6301  ->
                            match (uu____6300, uu____6301) with
                            | ((int_to_t1,x),(uu____6320,y)) ->
                                let uu____6330 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6330))) in
              let uu____6331 =
                let uu____6346 =
                  let uu____6359 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6359, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6379  ->
                            fun uu____6380  ->
                              match (uu____6379, uu____6380) with
                              | ((int_to_t1,x),(uu____6399,y)) ->
                                  let uu____6409 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6409))) in
                [uu____6346] in
              uu____6267 :: uu____6331 in
            uu____6188 :: uu____6252)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6499)::(a1,uu____6501)::(a2,uu____6503)::[] ->
        let uu____6540 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6540 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_6546 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_6546.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_6546.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6550 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6550.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6550.FStar_Syntax_Syntax.vars)
                })
         | uu____6551 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6553)::uu____6554::(a1,uu____6556)::(a2,uu____6558)::[] ->
        let uu____6607 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6607 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_6613 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_6613.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_6613.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6617 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6617.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6617.FStar_Syntax_Syntax.vars)
                })
         | uu____6618 -> FStar_Pervasives_Native.None)
    | uu____6619 -> failwith "Unexpected number of arguments" in
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
      let uu____6638 =
        let uu____6639 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6639 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6638
    with | uu____6645 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6649 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6649) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6709  ->
           fun subst1  ->
             match uu____6709 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6751)) ->
                      let uu____6810 = b in
                      (match uu____6810 with
                       | (bv,uu____6818) ->
                           let uu____6819 =
                             let uu____6820 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6820 in
                           if uu____6819
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6825 = unembed_binder term1 in
                              match uu____6825 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6832 =
                                      let uu___227_6833 = bv in
                                      let uu____6834 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___227_6833.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___227_6833.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6834
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6832 in
                                  let b_for_x =
                                    let uu____6838 =
                                      let uu____6845 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6845) in
                                    FStar_Syntax_Syntax.NT uu____6838 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___194_6854  ->
                                         match uu___194_6854 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6855,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6857;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6858;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6863 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6864 -> subst1)) env []
let reduce_primops:
  'Auu____6881 'Auu____6882 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6882) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6881 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6923 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6923
          then tm
          else
            (let uu____6925 = FStar_Syntax_Util.head_and_args tm in
             match uu____6925 with
             | (head1,args) ->
                 let uu____6962 =
                   let uu____6963 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6963.FStar_Syntax_Syntax.n in
                 (match uu____6962 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6967 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6967 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6984  ->
                                   let uu____6985 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6986 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6993 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6985 uu____6986 uu____6993);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6998  ->
                                   let uu____6999 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6999);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7002  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7004 =
                                 prim_step.interpretation psc args in
                               match uu____7004 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7010  ->
                                         let uu____7011 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7011);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7017  ->
                                         let uu____7018 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7019 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7018 uu____7019);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7020 ->
                           (log_primops cfg
                              (fun uu____7024  ->
                                 let uu____7025 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7025);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7029  ->
                            let uu____7030 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7030);
                       (match args with
                        | (a1,uu____7032)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7049 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7061  ->
                            let uu____7062 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7062);
                       (match args with
                        | (a1,uu____7064)::(a2,uu____7066)::[] ->
                            let uu____7093 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____7093 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___228_7097 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___228_7097.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___228_7097.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7100 -> tm))
                  | uu____7109 -> tm))
let reduce_equality:
  'Auu____7114 'Auu____7115 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7115) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7114 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___229_7153 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___229_7153.tcenv);
           delta_level = (uu___229_7153.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___229_7153.strong)
         }) tm
let maybe_simplify_aux:
  'Auu____7160 'Auu____7161 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7161) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7160 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7203 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7203
          then tm1
          else
            (let w t =
               let uu___230_7215 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___230_7215.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___230_7215.FStar_Syntax_Syntax.vars)
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
               | uu____7232 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7237 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7237
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7258 =
                 match uu____7258 with
                 | (t1,q) ->
                     let uu____7271 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7271 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7299 -> (t1, q)) in
               let uu____7308 = FStar_Syntax_Util.head_and_args t in
               match uu____7308 with
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
                         FStar_Syntax_Syntax.pos = uu____7405;
                         FStar_Syntax_Syntax.vars = uu____7406;_},uu____7407);
                    FStar_Syntax_Syntax.pos = uu____7408;
                    FStar_Syntax_Syntax.vars = uu____7409;_},args)
                 ->
                 let uu____7435 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7435
                 then
                   let uu____7436 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7436 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7491)::
                        (uu____7492,(arg,uu____7494))::[] ->
                        maybe_auto_squash arg
                    | (uu____7559,(arg,uu____7561))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7562)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7627)::uu____7628::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7691::(FStar_Pervasives_Native.Some (false
                                   ),uu____7692)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7755 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7771 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7771
                    then
                      let uu____7772 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7772 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7827)::uu____7828::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7891::(FStar_Pervasives_Native.Some (true
                                     ),uu____7892)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7955)::
                          (uu____7956,(arg,uu____7958))::[] ->
                          maybe_auto_squash arg
                      | (uu____8023,(arg,uu____8025))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8026)::[]
                          -> maybe_auto_squash arg
                      | uu____8091 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8107 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8107
                       then
                         let uu____8108 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8108 with
                         | uu____8163::(FStar_Pervasives_Native.Some (true
                                        ),uu____8164)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8227)::uu____8228::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8291)::
                             (uu____8292,(arg,uu____8294))::[] ->
                             maybe_auto_squash arg
                         | (uu____8359,(p,uu____8361))::(uu____8362,(q,uu____8364))::[]
                             ->
                             let uu____8429 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8429
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8431 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8447 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8447
                          then
                            let uu____8448 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8448 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8503)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8542)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8581 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8597 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8597
                             then
                               match args with
                               | (t,uu____8599)::[] ->
                                   let uu____8616 =
                                     let uu____8617 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8617.FStar_Syntax_Syntax.n in
                                   (match uu____8616 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8620::[],body,uu____8622) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8649 -> tm1)
                                    | uu____8652 -> tm1)
                               | (uu____8653,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8654))::
                                   (t,uu____8656)::[] ->
                                   let uu____8695 =
                                     let uu____8696 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8696.FStar_Syntax_Syntax.n in
                                   (match uu____8695 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8699::[],body,uu____8701) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8728 -> tm1)
                                    | uu____8731 -> tm1)
                               | uu____8732 -> tm1
                             else
                               (let uu____8742 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8742
                                then
                                  match args with
                                  | (t,uu____8744)::[] ->
                                      let uu____8761 =
                                        let uu____8762 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8762.FStar_Syntax_Syntax.n in
                                      (match uu____8761 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8765::[],body,uu____8767)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8794 -> tm1)
                                       | uu____8797 -> tm1)
                                  | (uu____8798,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8799))::(t,uu____8801)::[] ->
                                      let uu____8840 =
                                        let uu____8841 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8841.FStar_Syntax_Syntax.n in
                                      (match uu____8840 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8844::[],body,uu____8846)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8873 -> tm1)
                                       | uu____8876 -> tm1)
                                  | uu____8877 -> tm1
                                else
                                  (let uu____8887 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8887
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8888;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8889;_},uu____8890)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8907;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8908;_},uu____8909)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8926 -> tm1
                                   else
                                     (let uu____8936 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8936 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8956 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8966;
                    FStar_Syntax_Syntax.vars = uu____8967;_},args)
                 ->
                 let uu____8989 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8989
                 then
                   let uu____8990 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8990 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9045)::
                        (uu____9046,(arg,uu____9048))::[] ->
                        maybe_auto_squash arg
                    | (uu____9113,(arg,uu____9115))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9116)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9181)::uu____9182::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9245::(FStar_Pervasives_Native.Some (false
                                   ),uu____9246)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9309 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9325 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9325
                    then
                      let uu____9326 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9326 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9381)::uu____9382::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9445::(FStar_Pervasives_Native.Some (true
                                     ),uu____9446)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9509)::
                          (uu____9510,(arg,uu____9512))::[] ->
                          maybe_auto_squash arg
                      | (uu____9577,(arg,uu____9579))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9580)::[]
                          -> maybe_auto_squash arg
                      | uu____9645 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9661 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9661
                       then
                         let uu____9662 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9662 with
                         | uu____9717::(FStar_Pervasives_Native.Some (true
                                        ),uu____9718)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9781)::uu____9782::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9845)::
                             (uu____9846,(arg,uu____9848))::[] ->
                             maybe_auto_squash arg
                         | (uu____9913,(p,uu____9915))::(uu____9916,(q,uu____9918))::[]
                             ->
                             let uu____9983 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9983
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9985 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10001 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10001
                          then
                            let uu____10002 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10002 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10057)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10096)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10135 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10151 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10151
                             then
                               match args with
                               | (t,uu____10153)::[] ->
                                   let uu____10170 =
                                     let uu____10171 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10171.FStar_Syntax_Syntax.n in
                                   (match uu____10170 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10174::[],body,uu____10176) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10203 -> tm1)
                                    | uu____10206 -> tm1)
                               | (uu____10207,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10208))::
                                   (t,uu____10210)::[] ->
                                   let uu____10249 =
                                     let uu____10250 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10250.FStar_Syntax_Syntax.n in
                                   (match uu____10249 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10253::[],body,uu____10255) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10282 -> tm1)
                                    | uu____10285 -> tm1)
                               | uu____10286 -> tm1
                             else
                               (let uu____10296 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10296
                                then
                                  match args with
                                  | (t,uu____10298)::[] ->
                                      let uu____10315 =
                                        let uu____10316 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10316.FStar_Syntax_Syntax.n in
                                      (match uu____10315 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10319::[],body,uu____10321)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10348 -> tm1)
                                       | uu____10351 -> tm1)
                                  | (uu____10352,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10353))::(t,uu____10355)::[] ->
                                      let uu____10394 =
                                        let uu____10395 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10395.FStar_Syntax_Syntax.n in
                                      (match uu____10394 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10398::[],body,uu____10400)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10427 -> tm1)
                                       | uu____10430 -> tm1)
                                  | uu____10431 -> tm1
                                else
                                  (let uu____10441 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10441
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10442;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10443;_},uu____10444)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10461;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10462;_},uu____10463)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10480 -> tm1
                                   else
                                     (let uu____10490 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10490 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10510 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10519 -> tm1)
let maybe_simplify:
  'Auu____10526 'Auu____10527 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10527) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10526 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10570 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10570
           then
             let uu____10571 = FStar_Syntax_Print.term_to_string tm in
             let uu____10572 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10571 uu____10572
           else ());
          tm'
let is_norm_request:
  'Auu____10578 .
    FStar_Syntax_Syntax.term -> 'Auu____10578 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10591 =
        let uu____10598 =
          let uu____10599 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10599.FStar_Syntax_Syntax.n in
        (uu____10598, args) in
      match uu____10591 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10605::uu____10606::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10610::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10615::uu____10616::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10619 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___195_10630  ->
    match uu___195_10630 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10636 =
          let uu____10639 =
            let uu____10640 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10640 in
          [uu____10639] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10636
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10655 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10655) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10693 =
          let uu____10696 =
            let uu____10701 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10701 s in
          FStar_All.pipe_right uu____10696 FStar_Util.must in
        FStar_All.pipe_right uu____10693 tr_norm_steps in
      match args with
      | uu____10726::(tm,uu____10728)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10751)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10766)::uu____10767::(tm,uu____10769)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10809 =
              let uu____10812 = full_norm steps in parse_steps uu____10812 in
            Beta :: uu____10809 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10821 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___196_10838  ->
    match uu___196_10838 with
    | (App
        (uu____10841,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10842;
                       FStar_Syntax_Syntax.vars = uu____10843;_},uu____10844,uu____10845))::uu____10846
        -> true
    | uu____10853 -> false
let firstn:
  'Auu____10859 .
    Prims.int ->
      'Auu____10859 Prims.list ->
        ('Auu____10859 Prims.list,'Auu____10859 Prims.list)
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
          (uu____10895,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10896;
                         FStar_Syntax_Syntax.vars = uu____10897;_},uu____10898,uu____10899))::uu____10900
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10907 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11023  ->
               let uu____11024 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11025 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11026 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11033 =
                 let uu____11034 =
                   let uu____11037 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11037 in
                 stack_to_string uu____11034 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11024 uu____11025 uu____11026 uu____11033);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11060 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11085 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11102 =
                 let uu____11103 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11104 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11103 uu____11104 in
               failwith uu____11102
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11105 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11122 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11123 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11124;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11125;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11128;
                 FStar_Syntax_Syntax.fv_delta = uu____11129;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11130;
                 FStar_Syntax_Syntax.fv_delta = uu____11131;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11132);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11140 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11140 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11146  ->
                     let uu____11147 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11148 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11147 uu____11148);
                if b
                then
                  (let uu____11149 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11149 t1 fv)
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
                 let uu___231_11188 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___231_11188.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___231_11188.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11221 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11221) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___232_11229 = cfg in
                 let uu____11230 =
                   FStar_List.filter
                     (fun uu___197_11233  ->
                        match uu___197_11233 with
                        | UnfoldOnly uu____11234 -> false
                        | NoDeltaSteps  -> false
                        | uu____11237 -> true) cfg.steps in
                 {
                   steps = uu____11230;
                   tcenv = (uu___232_11229.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___232_11229.primitive_steps);
                   strong = (uu___232_11229.strong)
                 } in
               let uu____11238 = get_norm_request (norm cfg' env []) args in
               (match uu____11238 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11254 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___198_11259  ->
                                match uu___198_11259 with
                                | UnfoldUntil uu____11260 -> true
                                | UnfoldOnly uu____11261 -> true
                                | uu____11264 -> false)) in
                      if uu____11254
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___233_11269 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___233_11269.tcenv);
                        delta_level;
                        primitive_steps = (uu___233_11269.primitive_steps);
                        strong = (uu___233_11269.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____11280 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11280
                      then
                        let uu____11283 =
                          let uu____11284 =
                            let uu____11289 = FStar_Util.now () in
                            (t1, uu____11289) in
                          Debug uu____11284 in
                        uu____11283 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11291;
                  FStar_Syntax_Syntax.vars = uu____11292;_},a1::a2::rest)
               ->
               let uu____11340 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11340 with
                | (hd1,uu____11356) ->
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
                  FStar_Syntax_Syntax.pos = uu____11421;
                  FStar_Syntax_Syntax.vars = uu____11422;_},a1::a2::rest)
               ->
               let uu____11470 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11470 with
                | (hd1,uu____11486) ->
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
                  FStar_Syntax_Syntax.pos = uu____11551;
                  FStar_Syntax_Syntax.vars = uu____11552;_},a1::a2::a3::rest)
               ->
               let uu____11613 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11613 with
                | (hd1,uu____11629) ->
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
                    (FStar_Const.Const_reflect uu____11700);
                  FStar_Syntax_Syntax.pos = uu____11701;
                  FStar_Syntax_Syntax.vars = uu____11702;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11734 = FStar_List.tl stack in
               norm cfg env uu____11734 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11737;
                  FStar_Syntax_Syntax.vars = uu____11738;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11770 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11770 with
                | (reify_head,uu____11786) ->
                    let a1 =
                      let uu____11808 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11808 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11811);
                            FStar_Syntax_Syntax.pos = uu____11812;
                            FStar_Syntax_Syntax.vars = uu____11813;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11847 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11857 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11857
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11864 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11864
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11867 =
                      let uu____11874 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11874, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11867 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___199_11887  ->
                         match uu___199_11887 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11890 =
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
                 if uu____11890
                 then false
                 else
                   (let uu____11892 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___200_11899  ->
                              match uu___200_11899 with
                              | UnfoldOnly uu____11900 -> true
                              | uu____11903 -> false)) in
                    match uu____11892 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11907 -> should_delta) in
               (log cfg
                  (fun uu____11915  ->
                     let uu____11916 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11917 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11918 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11916 uu____11917 uu____11918);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11921 = lookup_bvar env x in
               (match uu____11921 with
                | Univ uu____11924 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11973 = FStar_ST.op_Bang r in
                      (match uu____11973 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12110  ->
                                 let uu____12111 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12112 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12111
                                   uu____12112);
                            (let uu____12113 =
                               let uu____12114 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12114.FStar_Syntax_Syntax.n in
                             match uu____12113 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12117 ->
                                 norm cfg env2 stack t'
                             | uu____12134 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12192)::uu____12193 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12202)::uu____12203 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12213,uu____12214))::stack_rest ->
                    (match c with
                     | Univ uu____12218 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12227 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12248  ->
                                    let uu____12249 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12249);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12289  ->
                                    let uu____12290 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12290);
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
                      (let uu___234_12340 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___234_12340.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___234_12340.strong)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12373  ->
                          let uu____12374 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12374);
                     norm cfg env stack1 t1)
                | (Debug uu____12375)::uu____12376 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12383 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12383
                    else
                      (let uu____12385 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12385 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12427  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12455 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12455
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12465 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12465)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12470 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12470.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12470.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12471 -> lopt in
                           (log cfg
                              (fun uu____12477  ->
                                 let uu____12478 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12478);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12491 = cfg in
                               {
                                 steps = (uu___236_12491.steps);
                                 tcenv = (uu___236_12491.tcenv);
                                 delta_level = (uu___236_12491.delta_level);
                                 primitive_steps =
                                   (uu___236_12491.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12502)::uu____12503 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12510 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12510
                    else
                      (let uu____12512 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12512 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12554  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12582 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12582
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12592 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12592)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12597 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12597.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12597.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12598 -> lopt in
                           (log cfg
                              (fun uu____12604  ->
                                 let uu____12605 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12605);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12618 = cfg in
                               {
                                 steps = (uu___236_12618.steps);
                                 tcenv = (uu___236_12618.tcenv);
                                 delta_level = (uu___236_12618.delta_level);
                                 primitive_steps =
                                   (uu___236_12618.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12629)::uu____12630 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12641 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12641
                    else
                      (let uu____12643 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12643 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12685  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12713 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12713
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12723 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12723)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12728 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12728.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12728.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12729 -> lopt in
                           (log cfg
                              (fun uu____12735  ->
                                 let uu____12736 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12736);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12749 = cfg in
                               {
                                 steps = (uu___236_12749.steps);
                                 tcenv = (uu___236_12749.tcenv);
                                 delta_level = (uu___236_12749.delta_level);
                                 primitive_steps =
                                   (uu___236_12749.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12760)::uu____12761 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12772 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12772
                    else
                      (let uu____12774 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12774 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12816  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12844 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12844
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12854 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12854)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12859 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12859.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12859.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12860 -> lopt in
                           (log cfg
                              (fun uu____12866  ->
                                 let uu____12867 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12867);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12880 = cfg in
                               {
                                 steps = (uu___236_12880.steps);
                                 tcenv = (uu___236_12880.tcenv);
                                 delta_level = (uu___236_12880.delta_level);
                                 primitive_steps =
                                   (uu___236_12880.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12891)::uu____12892 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12907 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12907
                    else
                      (let uu____12909 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12909 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12951  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12979 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12979
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12989 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12989)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12994 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12994.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12994.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12995 -> lopt in
                           (log cfg
                              (fun uu____13001  ->
                                 let uu____13002 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13002);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13015 = cfg in
                               {
                                 steps = (uu___236_13015.steps);
                                 tcenv = (uu___236_13015.tcenv);
                                 delta_level = (uu___236_13015.delta_level);
                                 primitive_steps =
                                   (uu___236_13015.primitive_steps);
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
                      let uu____13026 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13026
                    else
                      (let uu____13028 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13028 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13070  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13098 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13098
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13108 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13108)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13113 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13113.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13113.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13114 -> lopt in
                           (log cfg
                              (fun uu____13120  ->
                                 let uu____13121 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13121);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13134 = cfg in
                               {
                                 steps = (uu___236_13134.steps);
                                 tcenv = (uu___236_13134.tcenv);
                                 delta_level = (uu___236_13134.delta_level);
                                 primitive_steps =
                                   (uu___236_13134.primitive_steps);
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
                      (fun uu____13183  ->
                         fun stack1  ->
                           match uu____13183 with
                           | (a,aq) ->
                               let uu____13195 =
                                 let uu____13196 =
                                   let uu____13203 =
                                     let uu____13204 =
                                       let uu____13235 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13235, false) in
                                     Clos uu____13204 in
                                   (uu____13203, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13196 in
                               uu____13195 :: stack1) args) in
               (log cfg
                  (fun uu____13311  ->
                     let uu____13312 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13312);
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
                             ((let uu___237_13348 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___237_13348.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___237_13348.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13349 ->
                      let uu____13354 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13354)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13357 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13357 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13388 =
                          let uu____13389 =
                            let uu____13396 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___238_13398 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___238_13398.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___238_13398.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13396) in
                          FStar_Syntax_Syntax.Tm_refine uu____13389 in
                        mk uu____13388 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13417 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13417
               else
                 (let uu____13419 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13419 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13427 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13451  -> dummy :: env1) env) in
                        norm_comp cfg uu____13427 c1 in
                      let t2 =
                        let uu____13473 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13473 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13532)::uu____13533 ->
                    (log cfg
                       (fun uu____13544  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13545)::uu____13546 ->
                    (log cfg
                       (fun uu____13557  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13558,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13559;
                                   FStar_Syntax_Syntax.vars = uu____13560;_},uu____13561,uu____13562))::uu____13563
                    ->
                    (log cfg
                       (fun uu____13572  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13573)::uu____13574 ->
                    (log cfg
                       (fun uu____13585  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13586 ->
                    (log cfg
                       (fun uu____13589  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13593  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13610 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13610
                         | FStar_Util.Inr c ->
                             let uu____13618 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13618 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Steps (s,ps,dl))::stack1 ->
                           let t2 =
                             let uu____13641 =
                               let uu____13642 =
                                 let uu____13669 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13669, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13642 in
                             mk uu____13641 t1.FStar_Syntax_Syntax.pos in
                           norm
                             (let uu___239_13690 = cfg in
                              {
                                steps = s;
                                tcenv = (uu___239_13690.tcenv);
                                delta_level = dl;
                                primitive_steps = ps;
                                strong = (uu___239_13690.strong)
                              }) env stack1 t2
                       | uu____13691 ->
                           let uu____13692 =
                             let uu____13693 =
                               let uu____13694 =
                                 let uu____13721 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13721, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13694 in
                             mk uu____13693 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13692))))
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
                         let uu____13831 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13831 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___240_13851 = cfg in
                               let uu____13852 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___240_13851.steps);
                                 tcenv = uu____13852;
                                 delta_level = (uu___240_13851.delta_level);
                                 primitive_steps =
                                   (uu___240_13851.primitive_steps);
                                 strong = (uu___240_13851.strong)
                               } in
                             let norm1 t2 =
                               let uu____13857 =
                                 let uu____13858 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13858 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13857 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___241_13861 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___241_13861.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___241_13861.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13862 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13862
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13873,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13874;
                               FStar_Syntax_Syntax.lbunivs = uu____13875;
                               FStar_Syntax_Syntax.lbtyp = uu____13876;
                               FStar_Syntax_Syntax.lbeff = uu____13877;
                               FStar_Syntax_Syntax.lbdef = uu____13878;_}::uu____13879),uu____13880)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13916 =
                 (let uu____13919 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13919) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13921 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13921))) in
               if uu____13916
               then
                 let binder =
                   let uu____13923 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13923 in
                 let env1 =
                   let uu____13933 =
                     let uu____13940 =
                       let uu____13941 =
                         let uu____13972 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13972,
                           false) in
                       Clos uu____13941 in
                     ((FStar_Pervasives_Native.Some binder), uu____13940) in
                   uu____13933 :: env in
                 (log cfg
                    (fun uu____14057  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____14059 =
                    let uu____14064 =
                      let uu____14065 =
                        let uu____14066 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14066
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14065] in
                    FStar_Syntax_Subst.open_term uu____14064 body in
                  match uu____14059 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____14075  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____14083 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____14083 in
                          FStar_Util.Inl
                            (let uu___242_14093 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___242_14093.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___242_14093.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____14096  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___243_14098 = lb in
                           let uu____14099 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___243_14098.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___243_14098.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____14099
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____14134  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___244_14154 = cfg in
                           {
                             steps = (uu___244_14154.steps);
                             tcenv = (uu___244_14154.tcenv);
                             delta_level = (uu___244_14154.delta_level);
                             primitive_steps =
                               (uu___244_14154.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____14157  ->
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
               let uu____14174 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14174 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14210 =
                               let uu___245_14211 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___245_14211.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___245_14211.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14210 in
                           let uu____14212 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14212 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14238 =
                                   FStar_List.map (fun uu____14254  -> dummy)
                                     lbs1 in
                                 let uu____14255 =
                                   let uu____14264 =
                                     FStar_List.map
                                       (fun uu____14284  -> dummy) xs1 in
                                   FStar_List.append uu____14264 env in
                                 FStar_List.append uu____14238 uu____14255 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14308 =
                                       let uu___246_14309 = rc in
                                       let uu____14310 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___246_14309.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14310;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___246_14309.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14308
                                 | uu____14317 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___247_14321 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___247_14321.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___247_14321.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14331 =
                        FStar_List.map (fun uu____14347  -> dummy) lbs2 in
                      FStar_List.append uu____14331 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14355 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14355 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___248_14371 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___248_14371.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___248_14371.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14398 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14398
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14417 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14493  ->
                        match uu____14493 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___249_14614 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___249_14614.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___249_14614.FStar_Syntax_Syntax.sort)
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
               (match uu____14417 with
                | (rec_env,memos,uu____14811) ->
                    let uu____14864 =
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
                             let uu____15395 =
                               let uu____15402 =
                                 let uu____15403 =
                                   let uu____15434 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15434, false) in
                                 Clos uu____15403 in
                               (FStar_Pervasives_Native.None, uu____15402) in
                             uu____15395 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15539 =
                      let uu____15540 = should_reify cfg stack in
                      Prims.op_Negation uu____15540 in
                    if uu____15539
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____15550 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15550
                        then
                          let uu___250_15551 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___250_15551.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___250_15551.primitive_steps);
                            strong = (uu___250_15551.strong)
                          }
                        else
                          (let uu___251_15553 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___251_15553.tcenv);
                             delta_level = (uu___251_15553.delta_level);
                             primitive_steps =
                               (uu___251_15553.primitive_steps);
                             strong = (uu___251_15553.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15555 =
                         let uu____15556 = FStar_Syntax_Subst.compress head1 in
                         uu____15556.FStar_Syntax_Syntax.n in
                       match uu____15555 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15574 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15574 with
                            | (uu____15575,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15581 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15589 =
                                         let uu____15590 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15590.FStar_Syntax_Syntax.n in
                                       match uu____15589 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15596,uu____15597))
                                           ->
                                           let uu____15606 =
                                             let uu____15607 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15607.FStar_Syntax_Syntax.n in
                                           (match uu____15606 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15613,msrc,uu____15615))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15624 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15624
                                            | uu____15625 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15626 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15627 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15627 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___252_15632 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___252_15632.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___252_15632.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___252_15632.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15633 =
                                            FStar_List.tl stack in
                                          let uu____15634 =
                                            let uu____15635 =
                                              let uu____15638 =
                                                let uu____15639 =
                                                  let uu____15652 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15652) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15639 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15638 in
                                            uu____15635
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15633
                                            uu____15634
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15668 =
                                            let uu____15669 = is_return body in
                                            match uu____15669 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15673;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15674;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15679 -> false in
                                          if uu____15668
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
                                               let uu____15703 =
                                                 let uu____15706 =
                                                   let uu____15707 =
                                                     let uu____15724 =
                                                       let uu____15727 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15727] in
                                                     (uu____15724, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15707 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15706 in
                                               uu____15703
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15743 =
                                                 let uu____15744 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15744.FStar_Syntax_Syntax.n in
                                               match uu____15743 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15750::uu____15751::[])
                                                   ->
                                                   let uu____15758 =
                                                     let uu____15761 =
                                                       let uu____15762 =
                                                         let uu____15769 =
                                                           let uu____15772 =
                                                             let uu____15773
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15773 in
                                                           let uu____15774 =
                                                             let uu____15777
                                                               =
                                                               let uu____15778
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15778 in
                                                             [uu____15777] in
                                                           uu____15772 ::
                                                             uu____15774 in
                                                         (bind1, uu____15769) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15762 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15761 in
                                                   uu____15758
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15786 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15792 =
                                                 let uu____15795 =
                                                   let uu____15796 =
                                                     let uu____15811 =
                                                       let uu____15814 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15815 =
                                                         let uu____15818 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15819 =
                                                           let uu____15822 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15823 =
                                                             let uu____15826
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15827
                                                               =
                                                               let uu____15830
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15831
                                                                 =
                                                                 let uu____15834
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15834] in
                                                               uu____15830 ::
                                                                 uu____15831 in
                                                             uu____15826 ::
                                                               uu____15827 in
                                                           uu____15822 ::
                                                             uu____15823 in
                                                         uu____15818 ::
                                                           uu____15819 in
                                                       uu____15814 ::
                                                         uu____15815 in
                                                     (bind_inst, uu____15811) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15796 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15795 in
                                               uu____15792
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15842 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____15842 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15866 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15866 with
                            | (uu____15867,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15902 =
                                        let uu____15903 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15903.FStar_Syntax_Syntax.n in
                                      match uu____15902 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15909) -> t4
                                      | uu____15914 -> head2 in
                                    let uu____15915 =
                                      let uu____15916 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15916.FStar_Syntax_Syntax.n in
                                    match uu____15915 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15922 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15923 = maybe_extract_fv head2 in
                                  match uu____15923 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15933 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15933
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15938 =
                                          maybe_extract_fv head3 in
                                        match uu____15938 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15943 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15944 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15949 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15964 =
                                    match uu____15964 with
                                    | (e,q) ->
                                        let uu____15971 =
                                          let uu____15972 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15972.FStar_Syntax_Syntax.n in
                                        (match uu____15971 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15987 -> false) in
                                  let uu____15988 =
                                    let uu____15989 =
                                      let uu____15996 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15996 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15989 in
                                  if uu____15988
                                  then
                                    let uu____16001 =
                                      let uu____16002 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____16002 in
                                    failwith uu____16001
                                  else ());
                                 (let uu____16004 =
                                    maybe_unfold_action head_app in
                                  match uu____16004 with
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
                                      let uu____16043 = FStar_List.tl stack in
                                      norm cfg env uu____16043 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16057 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16057 in
                           let uu____16058 = FStar_List.tl stack in
                           norm cfg env uu____16058 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16179  ->
                                     match uu____16179 with
                                     | (pat,wopt,tm) ->
                                         let uu____16227 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16227))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16259 = FStar_List.tl stack in
                           norm cfg env uu____16259 tm
                       | uu____16260 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16268 = should_reify cfg stack in
                    if uu____16268
                    then
                      let uu____16269 = FStar_List.tl stack in
                      let uu____16270 =
                        let uu____16271 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16271 in
                      norm cfg env uu____16269 uu____16270
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16274 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16274
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___253_16283 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___253_16283.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___253_16283.primitive_steps);
                             strong = (uu___253_16283.strong)
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
                | uu____16285 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____16287::uu____16288 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16293) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16294 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____16325 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16339 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16339
                             | uu____16350 -> m in
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
              let uu____16362 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16362 in
            let uu____16363 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16363 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16376  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16387  ->
                      let uu____16388 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16389 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16388
                        uu____16389);
                 (let t1 =
                    let uu____16391 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16391
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
                    | (UnivArgs (us',uu____16401))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____16456 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____16459 ->
                        let uu____16462 =
                          let uu____16463 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16463 in
                        failwith uu____16462
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
              let uu____16473 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16473 with
              | (uu____16474,return_repr) ->
                  let return_inst =
                    let uu____16483 =
                      let uu____16484 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16484.FStar_Syntax_Syntax.n in
                    match uu____16483 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16490::[]) ->
                        let uu____16497 =
                          let uu____16500 =
                            let uu____16501 =
                              let uu____16508 =
                                let uu____16511 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16511] in
                              (return_tm, uu____16508) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16501 in
                          FStar_Syntax_Syntax.mk uu____16500 in
                        uu____16497 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16519 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16522 =
                    let uu____16525 =
                      let uu____16526 =
                        let uu____16541 =
                          let uu____16544 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16545 =
                            let uu____16548 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16548] in
                          uu____16544 :: uu____16545 in
                        (return_inst, uu____16541) in
                      FStar_Syntax_Syntax.Tm_app uu____16526 in
                    FStar_Syntax_Syntax.mk uu____16525 in
                  uu____16522 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16557 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16557 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16560 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16560
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16561;
                     FStar_TypeChecker_Env.mtarget = uu____16562;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16563;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16578;
                     FStar_TypeChecker_Env.mtarget = uu____16579;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16580;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16604 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16605 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16604 t FStar_Syntax_Syntax.tun uu____16605)
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
                (fun uu____16661  ->
                   match uu____16661 with
                   | (a,imp) ->
                       let uu____16672 = norm cfg env [] a in
                       (uu____16672, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___254_16689 = comp1 in
            let uu____16692 =
              let uu____16693 =
                let uu____16702 = norm cfg env [] t in
                let uu____16703 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16702, uu____16703) in
              FStar_Syntax_Syntax.Total uu____16693 in
            {
              FStar_Syntax_Syntax.n = uu____16692;
              FStar_Syntax_Syntax.pos =
                (uu___254_16689.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___254_16689.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___255_16718 = comp1 in
            let uu____16721 =
              let uu____16722 =
                let uu____16731 = norm cfg env [] t in
                let uu____16732 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16731, uu____16732) in
              FStar_Syntax_Syntax.GTotal uu____16722 in
            {
              FStar_Syntax_Syntax.n = uu____16721;
              FStar_Syntax_Syntax.pos =
                (uu___255_16718.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___255_16718.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16784  ->
                      match uu____16784 with
                      | (a,i) ->
                          let uu____16795 = norm cfg env [] a in
                          (uu____16795, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___201_16806  ->
                      match uu___201_16806 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16810 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16810
                      | f -> f)) in
            let uu___256_16814 = comp1 in
            let uu____16817 =
              let uu____16818 =
                let uu___257_16819 = ct in
                let uu____16820 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16821 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16824 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16820;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___257_16819.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16821;
                  FStar_Syntax_Syntax.effect_args = uu____16824;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16818 in
            {
              FStar_Syntax_Syntax.n = uu____16817;
              FStar_Syntax_Syntax.pos =
                (uu___256_16814.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___256_16814.FStar_Syntax_Syntax.vars)
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
            (let uu___258_16842 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___258_16842.tcenv);
               delta_level = (uu___258_16842.delta_level);
               primitive_steps = (uu___258_16842.primitive_steps);
               strong = (uu___258_16842.strong)
             }) env [] t in
        let non_info t =
          let uu____16847 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16847 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16850 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___259_16869 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___259_16869.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___259_16869.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16876 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16876
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
                    let uu___260_16887 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___260_16887.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___260_16887.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___260_16887.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___261_16889 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___261_16889.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___261_16889.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___261_16889.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___261_16889.FStar_Syntax_Syntax.flags)
                    } in
              let uu___262_16890 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___262_16890.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___262_16890.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16892 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16895  ->
        match uu____16895 with
        | (x,imp) ->
            let uu____16898 =
              let uu___263_16899 = x in
              let uu____16900 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___263_16899.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___263_16899.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16900
              } in
            (uu____16898, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16906 =
          FStar_List.fold_left
            (fun uu____16924  ->
               fun b  ->
                 match uu____16924 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16906 with | (nbs,uu____16964) -> FStar_List.rev nbs
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
            let uu____16980 =
              let uu___264_16981 = rc in
              let uu____16982 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___264_16981.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16982;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___264_16981.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16980
        | uu____16989 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17002  ->
               let uu____17003 = FStar_Syntax_Print.tag_of_term t in
               let uu____17004 = FStar_Syntax_Print.term_to_string t in
               let uu____17005 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17012 =
                 let uu____17013 =
                   let uu____17016 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17016 in
                 stack_to_string uu____17013 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____17003 uu____17004 uu____17005 uu____17012);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____17045 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____17045
                 then
                   let time_now = FStar_Util.now () in
                   let uu____17047 =
                     let uu____17048 =
                       let uu____17049 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17049 in
                     FStar_Util.string_of_int uu____17048 in
                   let uu____17054 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17055 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17047 uu____17054 uu____17055
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___265_17073 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___265_17073.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___265_17073.strong)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____17114  ->
                     let uu____17115 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17115);
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
               let uu____17151 =
                 let uu___266_17152 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___266_17152.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___266_17152.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____17151
           | (Arg (Univ uu____17153,uu____17154,uu____17155))::uu____17156 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17159,uu____17160))::uu____17161 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____17177),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17230  ->
                     let uu____17231 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17231);
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
                  (let uu____17241 = FStar_ST.op_Bang m in
                   match uu____17241 with
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
                   | FStar_Pervasives_Native.Some (uu____17385,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17428 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17428
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17440  ->
                     let uu____17441 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17441);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17446 =
                   log cfg
                     (fun uu____17451  ->
                        let uu____17452 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17453 =
                          let uu____17454 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17471  ->
                                    match uu____17471 with
                                    | (p,uu____17481,uu____17482) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17454
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17452 uu____17453);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___202_17499  ->
                                match uu___202_17499 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17500 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___267_17504 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___267_17504.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___267_17504.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17536 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17557 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17617  ->
                                    fun uu____17618  ->
                                      match (uu____17617, uu____17618) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17709 = norm_pat env3 p1 in
                                          (match uu____17709 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17557 with
                           | (pats1,env3) ->
                               ((let uu___268_17791 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___268_17791.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___269_17810 = x in
                            let uu____17811 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___269_17810.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___269_17810.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17811
                            } in
                          ((let uu___270_17825 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___270_17825.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___271_17836 = x in
                            let uu____17837 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___271_17836.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___271_17836.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17837
                            } in
                          ((let uu___272_17851 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___272_17851.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___273_17867 = x in
                            let uu____17868 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___273_17867.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___273_17867.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17868
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___274_17875 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___274_17875.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17885 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17899 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17899 with
                                  | (p,wopt,e) ->
                                      let uu____17919 = norm_pat env1 p in
                                      (match uu____17919 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17944 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17944 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17950 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17950) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17960) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17965 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17966;
                         FStar_Syntax_Syntax.fv_delta = uu____17967;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17968;
                         FStar_Syntax_Syntax.fv_delta = uu____17969;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17970);_}
                       -> true
                   | uu____17977 -> false in
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
                   let uu____18122 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18122 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18209 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18248 ->
                                 let uu____18249 =
                                   let uu____18250 = is_cons head1 in
                                   Prims.op_Negation uu____18250 in
                                 FStar_Util.Inr uu____18249)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18275 =
                              let uu____18276 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18276.FStar_Syntax_Syntax.n in
                            (match uu____18275 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18294 ->
                                 let uu____18295 =
                                   let uu____18296 = is_cons head1 in
                                   Prims.op_Negation uu____18296 in
                                 FStar_Util.Inr uu____18295))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18365)::rest_a,(p1,uu____18368)::rest_p) ->
                       let uu____18412 = matches_pat t1 p1 in
                       (match uu____18412 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18461 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18567 = matches_pat scrutinee1 p1 in
                       (match uu____18567 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18607  ->
                                  let uu____18608 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18609 =
                                    let uu____18610 =
                                      FStar_List.map
                                        (fun uu____18620  ->
                                           match uu____18620 with
                                           | (uu____18625,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18610
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18608 uu____18609);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18656  ->
                                       match uu____18656 with
                                       | (bv,t1) ->
                                           let uu____18679 =
                                             let uu____18686 =
                                               let uu____18689 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18689 in
                                             let uu____18690 =
                                               let uu____18691 =
                                                 let uu____18722 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18722, false) in
                                               Clos uu____18691 in
                                             (uu____18686, uu____18690) in
                                           uu____18679 :: env2) env1 s in
                              let uu____18831 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18831))) in
                 let uu____18832 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18832
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___203_18853  ->
                match uu___203_18853 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18857 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18863 -> d in
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
            let uu___275_18888 = config s e in
            {
              steps = (uu___275_18888.steps);
              tcenv = (uu___275_18888.tcenv);
              delta_level = (uu___275_18888.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___275_18888.strong)
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
      fun t  -> let uu____18913 = config s e in norm_comp uu____18913 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18926 = config [] env in norm_universe uu____18926 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18939 = config [] env in ghost_to_pure_aux uu____18939 [] c
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
        let uu____18957 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18957 in
      let uu____18964 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18964
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___276_18966 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___276_18966.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___276_18966.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18969  ->
                    let uu____18970 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18970))
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
            ((let uu____18987 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18987);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18998 = config [AllowUnboundUniverses] env in
          norm_comp uu____18998 [] c
        with
        | e ->
            ((let uu____19011 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19011);
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
                   let uu____19048 =
                     let uu____19049 =
                       let uu____19056 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____19056) in
                     FStar_Syntax_Syntax.Tm_refine uu____19049 in
                   mk uu____19048 t01.FStar_Syntax_Syntax.pos
               | uu____19061 -> t2)
          | uu____19062 -> t2 in
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
        let uu____19102 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19102 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19131 ->
                 let uu____19138 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19138 with
                  | (actuals,uu____19148,uu____19149) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19163 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19163 with
                         | (binders,args) ->
                             let uu____19180 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19180
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
      | uu____19188 ->
          let uu____19189 = FStar_Syntax_Util.head_and_args t in
          (match uu____19189 with
           | (head1,args) ->
               let uu____19226 =
                 let uu____19227 = FStar_Syntax_Subst.compress head1 in
                 uu____19227.FStar_Syntax_Syntax.n in
               (match uu____19226 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19230,thead) ->
                    let uu____19256 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19256 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19298 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___281_19306 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___281_19306.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___281_19306.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___281_19306.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___281_19306.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___281_19306.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___281_19306.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___281_19306.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___281_19306.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___281_19306.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___281_19306.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___281_19306.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___281_19306.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___281_19306.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___281_19306.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___281_19306.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___281_19306.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___281_19306.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___281_19306.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___281_19306.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___281_19306.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___281_19306.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___281_19306.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___281_19306.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___281_19306.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___281_19306.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___281_19306.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___281_19306.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___281_19306.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___281_19306.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___281_19306.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___281_19306.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19298 with
                            | (uu____19307,ty,uu____19309) ->
                                eta_expand_with_type env t ty))
                | uu____19310 ->
                    let uu____19311 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___282_19319 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___282_19319.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___282_19319.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___282_19319.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___282_19319.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___282_19319.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___282_19319.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___282_19319.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___282_19319.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___282_19319.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___282_19319.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___282_19319.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___282_19319.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___282_19319.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___282_19319.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___282_19319.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___282_19319.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___282_19319.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___282_19319.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___282_19319.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___282_19319.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___282_19319.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___282_19319.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___282_19319.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___282_19319.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___282_19319.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___282_19319.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___282_19319.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___282_19319.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___282_19319.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___282_19319.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___282_19319.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19311 with
                     | (uu____19320,ty,uu____19322) ->
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
            | (uu____19396,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19402,FStar_Util.Inl t) ->
                let uu____19408 =
                  let uu____19411 =
                    let uu____19412 =
                      let uu____19425 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19425) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19412 in
                  FStar_Syntax_Syntax.mk uu____19411 in
                uu____19408 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19429 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19429 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19456 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19511 ->
                    let uu____19512 =
                      let uu____19521 =
                        let uu____19522 = FStar_Syntax_Subst.compress t3 in
                        uu____19522.FStar_Syntax_Syntax.n in
                      (uu____19521, tc) in
                    (match uu____19512 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19547) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19584) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19623,FStar_Util.Inl uu____19624) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19647 -> failwith "Impossible") in
              (match uu____19456 with
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
          let uu____19752 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19752 with
          | (univ_names1,binders1,tc) ->
              let uu____19810 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19810)
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
          let uu____19845 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19845 with
          | (univ_names1,binders1,tc) ->
              let uu____19905 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19905)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19938 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19938 with
           | (univ_names1,binders1,typ1) ->
               let uu___283_19966 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_19966.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_19966.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_19966.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_19966.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___284_19987 = s in
          let uu____19988 =
            let uu____19989 =
              let uu____19998 = FStar_List.map (elim_uvars env) sigs in
              (uu____19998, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19989 in
          {
            FStar_Syntax_Syntax.sigel = uu____19988;
            FStar_Syntax_Syntax.sigrng =
              (uu___284_19987.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___284_19987.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___284_19987.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___284_19987.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20015 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20015 with
           | (univ_names1,uu____20033,typ1) ->
               let uu___285_20047 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___285_20047.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___285_20047.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___285_20047.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___285_20047.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20053 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20053 with
           | (univ_names1,uu____20071,typ1) ->
               let uu___286_20085 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___286_20085.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___286_20085.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___286_20085.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___286_20085.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20119 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20119 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20142 =
                            let uu____20143 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20143 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20142 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___287_20146 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___287_20146.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___287_20146.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___288_20147 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___288_20147.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___288_20147.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___288_20147.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___288_20147.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___289_20159 = s in
          let uu____20160 =
            let uu____20161 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20161 in
          {
            FStar_Syntax_Syntax.sigel = uu____20160;
            FStar_Syntax_Syntax.sigrng =
              (uu___289_20159.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___289_20159.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___289_20159.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___289_20159.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20165 = elim_uvars_aux_t env us [] t in
          (match uu____20165 with
           | (us1,uu____20183,t1) ->
               let uu___290_20197 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___290_20197.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___290_20197.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___290_20197.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___290_20197.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20198 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20200 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20200 with
           | (univs1,binders,signature) ->
               let uu____20228 =
                 let uu____20237 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20237 with
                 | (univs_opening,univs2) ->
                     let uu____20264 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20264) in
               (match uu____20228 with
                | (univs_opening,univs_closing) ->
                    let uu____20281 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20287 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20288 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20287, uu____20288) in
                    (match uu____20281 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20310 =
                           match uu____20310 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20328 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20328 with
                                | (us1,t1) ->
                                    let uu____20339 =
                                      let uu____20344 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20351 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20344, uu____20351) in
                                    (match uu____20339 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20364 =
                                           let uu____20369 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20378 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20369, uu____20378) in
                                         (match uu____20364 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20394 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20394 in
                                              let uu____20395 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20395 with
                                               | (uu____20416,uu____20417,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20432 =
                                                       let uu____20433 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20433 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20432 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20438 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20438 with
                           | (uu____20451,uu____20452,t1) -> t1 in
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
                             | uu____20512 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20529 =
                               let uu____20530 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20530.FStar_Syntax_Syntax.n in
                             match uu____20529 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20589 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20618 =
                               let uu____20619 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20619.FStar_Syntax_Syntax.n in
                             match uu____20618 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20640) ->
                                 let uu____20661 = destruct_action_body body in
                                 (match uu____20661 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20706 ->
                                 let uu____20707 = destruct_action_body t in
                                 (match uu____20707 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20756 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20756 with
                           | (action_univs,t) ->
                               let uu____20765 = destruct_action_typ_templ t in
                               (match uu____20765 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___291_20806 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___291_20806.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___291_20806.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___292_20808 = ed in
                           let uu____20809 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20810 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20811 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20812 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20813 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20814 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20815 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20816 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20817 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20818 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20819 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20820 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20821 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20822 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___292_20808.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___292_20808.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20809;
                             FStar_Syntax_Syntax.bind_wp = uu____20810;
                             FStar_Syntax_Syntax.if_then_else = uu____20811;
                             FStar_Syntax_Syntax.ite_wp = uu____20812;
                             FStar_Syntax_Syntax.stronger = uu____20813;
                             FStar_Syntax_Syntax.close_wp = uu____20814;
                             FStar_Syntax_Syntax.assert_p = uu____20815;
                             FStar_Syntax_Syntax.assume_p = uu____20816;
                             FStar_Syntax_Syntax.null_wp = uu____20817;
                             FStar_Syntax_Syntax.trivial = uu____20818;
                             FStar_Syntax_Syntax.repr = uu____20819;
                             FStar_Syntax_Syntax.return_repr = uu____20820;
                             FStar_Syntax_Syntax.bind_repr = uu____20821;
                             FStar_Syntax_Syntax.actions = uu____20822
                           } in
                         let uu___293_20825 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___293_20825.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___293_20825.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___293_20825.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___293_20825.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___204_20842 =
            match uu___204_20842 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20869 = elim_uvars_aux_t env us [] t in
                (match uu____20869 with
                 | (us1,uu____20893,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___294_20912 = sub_eff in
            let uu____20913 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20916 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___294_20912.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___294_20912.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20913;
              FStar_Syntax_Syntax.lift = uu____20916
            } in
          let uu___295_20919 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___295_20919.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___295_20919.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___295_20919.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___295_20919.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20929 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20929 with
           | (univ_names1,binders1,comp1) ->
               let uu___296_20963 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___296_20963.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___296_20963.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___296_20963.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___296_20963.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20974 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t