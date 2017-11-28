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
let maybe_simplify:
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
             let is_squashed t =
               let uu____7237 = FStar_Syntax_Util.head_and_args t in
               match uu____7237 with
               | (head1,uu____7253) ->
                   let uu____7274 =
                     let uu____7275 = FStar_Syntax_Util.un_uinst head1 in
                     uu____7275.FStar_Syntax_Syntax.n in
                   (match uu____7274 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        (((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.squash_lid)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.and_lid))
                                     ||
                                     (FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.or_lid))
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.not_lid))
                                   ||
                                   (FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.imp_lid))
                                  ||
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.iff_lid))
                                 ||
                                 (FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.ite_lid))
                                ||
                                (FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.exists_lid))
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.forall_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.true_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.false_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.eq2_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.eq3_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.b2t_lid)
                    | uu____7279 -> false) in
             let maybe_squash t =
               let uu____7284 = is_squashed t in
               if uu____7284
               then t
               else FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero t in
             let squashed_head_unsquash_args t =
               let maybe_unsquash_arg uu____7305 =
                 match uu____7305 with
                 | (t1,q) ->
                     let uu____7318 = FStar_Syntax_Util.head_and_args t1 in
                     (match uu____7318 with
                      | (head1,args) ->
                          let uu____7361 =
                            let uu____7374 =
                              let uu____7375 =
                                FStar_Syntax_Subst.compress head1 in
                              uu____7375.FStar_Syntax_Syntax.n in
                            (uu____7374, args) in
                          (match uu____7361 with
                           | (FStar_Syntax_Syntax.Tm_uinst
                              ({
                                 FStar_Syntax_Syntax.n =
                                   FStar_Syntax_Syntax.Tm_fvar fv;
                                 FStar_Syntax_Syntax.pos = uu____7393;
                                 FStar_Syntax_Syntax.vars = uu____7394;_},(FStar_Syntax_Syntax.U_zero
                               )::[]),(t2,uu____7396)::[]) when
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.squash_lid
                               -> (t2, q)
                           | uu____7429 -> (t1, q))) in
               let uu____7442 = FStar_Syntax_Util.head_and_args t in
               match uu____7442 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_unsquash_arg args in
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
                         FStar_Syntax_Syntax.pos = uu____7539;
                         FStar_Syntax_Syntax.vars = uu____7540;_},uu____7541);
                    FStar_Syntax_Syntax.pos = uu____7542;
                    FStar_Syntax_Syntax.vars = uu____7543;_},args)
                 ->
                 let uu____7569 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7569
                 then
                   let uu____7570 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7570 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7625)::
                        (uu____7626,(arg,uu____7628))::[] -> maybe_squash arg
                    | (uu____7693,(arg,uu____7695))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7696)::[]
                        -> maybe_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7761)::uu____7762::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7825::(FStar_Pervasives_Native.Some (false
                                   ),uu____7826)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7889 -> squashed_head_unsquash_args tm1)
                 else
                   (let uu____7905 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7905
                    then
                      let uu____7906 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7906 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7961)::uu____7962::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8025::(FStar_Pervasives_Native.Some (true
                                     ),uu____8026)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8089)::
                          (uu____8090,(arg,uu____8092))::[] ->
                          maybe_squash arg
                      | (uu____8157,(arg,uu____8159))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8160)::[]
                          -> maybe_squash arg
                      | uu____8225 -> squashed_head_unsquash_args tm1
                    else
                      (let uu____8241 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8241
                       then
                         let uu____8242 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8242 with
                         | uu____8297::(FStar_Pervasives_Native.Some (true
                                        ),uu____8298)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8361)::uu____8362::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8425)::
                             (uu____8426,(arg,uu____8428))::[] ->
                             maybe_squash arg
                         | (uu____8493,(p,uu____8495))::(uu____8496,(q,uu____8498))::[]
                             ->
                             let uu____8563 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8563
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_unsquash_args tm1)
                         | uu____8565 -> squashed_head_unsquash_args tm1
                       else
                         (let uu____8581 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8581
                          then
                            let uu____8582 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8582 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8637)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8676)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8715 -> squashed_head_unsquash_args tm1
                          else
                            (let uu____8731 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8731
                             then
                               match args with
                               | (t,uu____8733)::[] ->
                                   let uu____8750 =
                                     let uu____8751 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8751.FStar_Syntax_Syntax.n in
                                   (match uu____8750 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8754::[],body,uu____8756) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8783 -> tm1)
                                    | uu____8786 -> tm1)
                               | (uu____8787,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8788))::
                                   (t,uu____8790)::[] ->
                                   let uu____8829 =
                                     let uu____8830 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8830.FStar_Syntax_Syntax.n in
                                   (match uu____8829 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8833::[],body,uu____8835) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8862 -> tm1)
                                    | uu____8865 -> tm1)
                               | uu____8866 -> tm1
                             else
                               (let uu____8876 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8876
                                then
                                  match args with
                                  | (t,uu____8878)::[] ->
                                      let uu____8895 =
                                        let uu____8896 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8896.FStar_Syntax_Syntax.n in
                                      (match uu____8895 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8899::[],body,uu____8901)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8928 -> tm1)
                                       | uu____8931 -> tm1)
                                  | (uu____8932,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8933))::(t,uu____8935)::[] ->
                                      let uu____8974 =
                                        let uu____8975 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8975.FStar_Syntax_Syntax.n in
                                      (match uu____8974 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8978::[],body,uu____8980)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9007 -> tm1)
                                       | uu____9010 -> tm1)
                                  | uu____9011 -> tm1
                                else
                                  (let uu____9021 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9021
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9022;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9023;_},uu____9024)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9041;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9042;_},uu____9043)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9060 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9071;
                    FStar_Syntax_Syntax.vars = uu____9072;_},args)
                 ->
                 let uu____9094 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9094
                 then
                   let uu____9095 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9095 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9150)::
                        (uu____9151,(arg,uu____9153))::[] -> maybe_squash arg
                    | (uu____9218,(arg,uu____9220))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9221)::[]
                        -> maybe_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9286)::uu____9287::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9350::(FStar_Pervasives_Native.Some (false
                                   ),uu____9351)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9414 -> squashed_head_unsquash_args tm1)
                 else
                   (let uu____9430 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9430
                    then
                      let uu____9431 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9431 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9486)::uu____9487::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9550::(FStar_Pervasives_Native.Some (true
                                     ),uu____9551)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9614)::
                          (uu____9615,(arg,uu____9617))::[] ->
                          maybe_squash arg
                      | (uu____9682,(arg,uu____9684))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9685)::[]
                          -> maybe_squash arg
                      | uu____9750 -> squashed_head_unsquash_args tm1
                    else
                      (let uu____9766 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9766
                       then
                         let uu____9767 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9767 with
                         | uu____9822::(FStar_Pervasives_Native.Some (true
                                        ),uu____9823)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9886)::uu____9887::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9950)::
                             (uu____9951,(arg,uu____9953))::[] ->
                             maybe_squash arg
                         | (uu____10018,(p,uu____10020))::(uu____10021,
                                                           (q,uu____10023))::[]
                             ->
                             let uu____10088 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10088
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_unsquash_args tm1)
                         | uu____10090 -> squashed_head_unsquash_args tm1
                       else
                         (let uu____10106 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10106
                          then
                            let uu____10107 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10107 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10162)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10201)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10240 -> squashed_head_unsquash_args tm1
                          else
                            (let uu____10256 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10256
                             then
                               match args with
                               | (t,uu____10258)::[] ->
                                   let uu____10275 =
                                     let uu____10276 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10276.FStar_Syntax_Syntax.n in
                                   (match uu____10275 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10279::[],body,uu____10281) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10308 -> tm1)
                                    | uu____10311 -> tm1)
                               | (uu____10312,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10313))::
                                   (t,uu____10315)::[] ->
                                   let uu____10354 =
                                     let uu____10355 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10355.FStar_Syntax_Syntax.n in
                                   (match uu____10354 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10358::[],body,uu____10360) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10387 -> tm1)
                                    | uu____10390 -> tm1)
                               | uu____10391 -> tm1
                             else
                               (let uu____10401 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10401
                                then
                                  match args with
                                  | (t,uu____10403)::[] ->
                                      let uu____10420 =
                                        let uu____10421 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10421.FStar_Syntax_Syntax.n in
                                      (match uu____10420 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10424::[],body,uu____10426)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10453 -> tm1)
                                       | uu____10456 -> tm1)
                                  | (uu____10457,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10458))::(t,uu____10460)::[] ->
                                      let uu____10499 =
                                        let uu____10500 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10500.FStar_Syntax_Syntax.n in
                                      (match uu____10499 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10503::[],body,uu____10505)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10532 -> tm1)
                                       | uu____10535 -> tm1)
                                  | uu____10536 -> tm1
                                else
                                  (let uu____10546 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10546
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10547;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10548;_},uu____10549)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10566;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10567;_},uu____10568)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10585 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | uu____10595 -> tm1)
let is_norm_request:
  'Auu____10599 .
    FStar_Syntax_Syntax.term -> 'Auu____10599 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10612 =
        let uu____10619 =
          let uu____10620 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10620.FStar_Syntax_Syntax.n in
        (uu____10619, args) in
      match uu____10612 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10626::uu____10627::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10631::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10636::uu____10637::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10640 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___195_10651  ->
    match uu___195_10651 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10657 =
          let uu____10660 =
            let uu____10661 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10661 in
          [uu____10660] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10657
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10676 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10676) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10714 =
          let uu____10717 =
            let uu____10722 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10722 s in
          FStar_All.pipe_right uu____10717 FStar_Util.must in
        FStar_All.pipe_right uu____10714 tr_norm_steps in
      match args with
      | uu____10747::(tm,uu____10749)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10772)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10787)::uu____10788::(tm,uu____10790)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10830 =
              let uu____10833 = full_norm steps in parse_steps uu____10833 in
            Beta :: uu____10830 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10842 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___196_10859  ->
    match uu___196_10859 with
    | (App
        (uu____10862,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10863;
                       FStar_Syntax_Syntax.vars = uu____10864;_},uu____10865,uu____10866))::uu____10867
        -> true
    | uu____10874 -> false
let firstn:
  'Auu____10880 .
    Prims.int ->
      'Auu____10880 Prims.list ->
        ('Auu____10880 Prims.list,'Auu____10880 Prims.list)
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
          (uu____10916,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10917;
                         FStar_Syntax_Syntax.vars = uu____10918;_},uu____10919,uu____10920))::uu____10921
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10928 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11044  ->
               let uu____11045 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11046 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11047 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11054 =
                 let uu____11055 =
                   let uu____11058 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11058 in
                 stack_to_string uu____11055 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11045 uu____11046 uu____11047 uu____11054);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11081 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11106 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11123 =
                 let uu____11124 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11125 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11124 uu____11125 in
               failwith uu____11123
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11126 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11143 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11144 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11145;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11146;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11149;
                 FStar_Syntax_Syntax.fv_delta = uu____11150;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11151;
                 FStar_Syntax_Syntax.fv_delta = uu____11152;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11153);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11161 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11161 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11167  ->
                     let uu____11168 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11169 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11168 uu____11169);
                if b
                then
                  (let uu____11170 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11170 t1 fv)
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
                 let uu___231_11209 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___231_11209.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___231_11209.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11242 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11242) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___232_11250 = cfg in
                 let uu____11251 =
                   FStar_List.filter
                     (fun uu___197_11254  ->
                        match uu___197_11254 with
                        | UnfoldOnly uu____11255 -> false
                        | NoDeltaSteps  -> false
                        | uu____11258 -> true) cfg.steps in
                 {
                   steps = uu____11251;
                   tcenv = (uu___232_11250.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___232_11250.primitive_steps);
                   strong = (uu___232_11250.strong)
                 } in
               let uu____11259 = get_norm_request (norm cfg' env []) args in
               (match uu____11259 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11275 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___198_11280  ->
                                match uu___198_11280 with
                                | UnfoldUntil uu____11281 -> true
                                | UnfoldOnly uu____11282 -> true
                                | uu____11285 -> false)) in
                      if uu____11275
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___233_11290 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___233_11290.tcenv);
                        delta_level;
                        primitive_steps = (uu___233_11290.primitive_steps);
                        strong = (uu___233_11290.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____11301 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11301
                      then
                        let uu____11304 =
                          let uu____11305 =
                            let uu____11310 = FStar_Util.now () in
                            (t1, uu____11310) in
                          Debug uu____11305 in
                        uu____11304 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11312;
                  FStar_Syntax_Syntax.vars = uu____11313;_},a1::a2::rest)
               ->
               let uu____11361 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11361 with
                | (hd1,uu____11377) ->
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
                  FStar_Syntax_Syntax.pos = uu____11442;
                  FStar_Syntax_Syntax.vars = uu____11443;_},a1::a2::rest)
               ->
               let uu____11491 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11491 with
                | (hd1,uu____11507) ->
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
                  FStar_Syntax_Syntax.pos = uu____11572;
                  FStar_Syntax_Syntax.vars = uu____11573;_},a1::a2::a3::rest)
               ->
               let uu____11634 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11634 with
                | (hd1,uu____11650) ->
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
                    (FStar_Const.Const_reflect uu____11721);
                  FStar_Syntax_Syntax.pos = uu____11722;
                  FStar_Syntax_Syntax.vars = uu____11723;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11755 = FStar_List.tl stack in
               norm cfg env uu____11755 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11758;
                  FStar_Syntax_Syntax.vars = uu____11759;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11791 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11791 with
                | (reify_head,uu____11807) ->
                    let a1 =
                      let uu____11829 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11829 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11832);
                            FStar_Syntax_Syntax.pos = uu____11833;
                            FStar_Syntax_Syntax.vars = uu____11834;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11868 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11878 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11878
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11885 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11885
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11888 =
                      let uu____11895 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11895, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11888 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___199_11908  ->
                         match uu___199_11908 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11911 =
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
                 if uu____11911
                 then false
                 else
                   (let uu____11913 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___200_11920  ->
                              match uu___200_11920 with
                              | UnfoldOnly uu____11921 -> true
                              | uu____11924 -> false)) in
                    match uu____11913 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11928 -> should_delta) in
               (log cfg
                  (fun uu____11936  ->
                     let uu____11937 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11938 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11939 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11937 uu____11938 uu____11939);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11942 = lookup_bvar env x in
               (match uu____11942 with
                | Univ uu____11945 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11994 = FStar_ST.op_Bang r in
                      (match uu____11994 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12131  ->
                                 let uu____12132 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12133 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12132
                                   uu____12133);
                            (let uu____12134 =
                               let uu____12135 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12135.FStar_Syntax_Syntax.n in
                             match uu____12134 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12138 ->
                                 norm cfg env2 stack t'
                             | uu____12155 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12213)::uu____12214 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12223)::uu____12224 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12234,uu____12235))::stack_rest ->
                    (match c with
                     | Univ uu____12239 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12248 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12269  ->
                                    let uu____12270 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12270);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12310  ->
                                    let uu____12311 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12311);
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
                      (let uu___234_12361 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___234_12361.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___234_12361.strong)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12394  ->
                          let uu____12395 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12395);
                     norm cfg env stack1 t1)
                | (Debug uu____12396)::uu____12397 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12404 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12404
                    else
                      (let uu____12406 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12406 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12448  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12476 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12476
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12486 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12486)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12491 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12491.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12491.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12492 -> lopt in
                           (log cfg
                              (fun uu____12498  ->
                                 let uu____12499 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12499);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12512 = cfg in
                               {
                                 steps = (uu___236_12512.steps);
                                 tcenv = (uu___236_12512.tcenv);
                                 delta_level = (uu___236_12512.delta_level);
                                 primitive_steps =
                                   (uu___236_12512.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12523)::uu____12524 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12531 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12531
                    else
                      (let uu____12533 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12533 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12575  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12603 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12603
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12613 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12613)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12618 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12618.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12618.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12619 -> lopt in
                           (log cfg
                              (fun uu____12625  ->
                                 let uu____12626 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12626);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12639 = cfg in
                               {
                                 steps = (uu___236_12639.steps);
                                 tcenv = (uu___236_12639.tcenv);
                                 delta_level = (uu___236_12639.delta_level);
                                 primitive_steps =
                                   (uu___236_12639.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12650)::uu____12651 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12662 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12662
                    else
                      (let uu____12664 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12664 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12706  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12734 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12734
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12744 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12744)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12749 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12749.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12749.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12750 -> lopt in
                           (log cfg
                              (fun uu____12756  ->
                                 let uu____12757 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12757);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12770 = cfg in
                               {
                                 steps = (uu___236_12770.steps);
                                 tcenv = (uu___236_12770.tcenv);
                                 delta_level = (uu___236_12770.delta_level);
                                 primitive_steps =
                                   (uu___236_12770.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12781)::uu____12782 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12793 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12793
                    else
                      (let uu____12795 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12795 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12837  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12865 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12865
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12875 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12875)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12880 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12880.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12880.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12881 -> lopt in
                           (log cfg
                              (fun uu____12887  ->
                                 let uu____12888 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12888);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12901 = cfg in
                               {
                                 steps = (uu___236_12901.steps);
                                 tcenv = (uu___236_12901.tcenv);
                                 delta_level = (uu___236_12901.delta_level);
                                 primitive_steps =
                                   (uu___236_12901.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12912)::uu____12913 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12928 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12928
                    else
                      (let uu____12930 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12930 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12972  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13000 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13000
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13010 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13010)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13015 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13015.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13015.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13016 -> lopt in
                           (log cfg
                              (fun uu____13022  ->
                                 let uu____13023 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13023);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13036 = cfg in
                               {
                                 steps = (uu___236_13036.steps);
                                 tcenv = (uu___236_13036.tcenv);
                                 delta_level = (uu___236_13036.delta_level);
                                 primitive_steps =
                                   (uu___236_13036.primitive_steps);
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
                      let uu____13047 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13047
                    else
                      (let uu____13049 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13049 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13091  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13119 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13119
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13129 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13129)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13134 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13134.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13134.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13135 -> lopt in
                           (log cfg
                              (fun uu____13141  ->
                                 let uu____13142 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13142);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13155 = cfg in
                               {
                                 steps = (uu___236_13155.steps);
                                 tcenv = (uu___236_13155.tcenv);
                                 delta_level = (uu___236_13155.delta_level);
                                 primitive_steps =
                                   (uu___236_13155.primitive_steps);
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
                      (fun uu____13204  ->
                         fun stack1  ->
                           match uu____13204 with
                           | (a,aq) ->
                               let uu____13216 =
                                 let uu____13217 =
                                   let uu____13224 =
                                     let uu____13225 =
                                       let uu____13256 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13256, false) in
                                     Clos uu____13225 in
                                   (uu____13224, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13217 in
                               uu____13216 :: stack1) args) in
               (log cfg
                  (fun uu____13332  ->
                     let uu____13333 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13333);
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
                             ((let uu___237_13369 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___237_13369.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___237_13369.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13370 ->
                      let uu____13375 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13375)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13378 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13378 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13409 =
                          let uu____13410 =
                            let uu____13417 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___238_13419 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___238_13419.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___238_13419.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13417) in
                          FStar_Syntax_Syntax.Tm_refine uu____13410 in
                        mk uu____13409 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13438 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13438
               else
                 (let uu____13440 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13440 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13448 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13472  -> dummy :: env1) env) in
                        norm_comp cfg uu____13448 c1 in
                      let t2 =
                        let uu____13494 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13494 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13553)::uu____13554 ->
                    (log cfg
                       (fun uu____13565  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13566)::uu____13567 ->
                    (log cfg
                       (fun uu____13578  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13579,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13580;
                                   FStar_Syntax_Syntax.vars = uu____13581;_},uu____13582,uu____13583))::uu____13584
                    ->
                    (log cfg
                       (fun uu____13593  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13594)::uu____13595 ->
                    (log cfg
                       (fun uu____13606  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13607 ->
                    (log cfg
                       (fun uu____13610  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13614  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13631 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13631
                         | FStar_Util.Inr c ->
                             let uu____13639 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13639 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Steps (s,ps,dl))::stack1 ->
                           let t2 =
                             let uu____13662 =
                               let uu____13663 =
                                 let uu____13690 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13690, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13663 in
                             mk uu____13662 t1.FStar_Syntax_Syntax.pos in
                           norm
                             (let uu___239_13711 = cfg in
                              {
                                steps = s;
                                tcenv = (uu___239_13711.tcenv);
                                delta_level = dl;
                                primitive_steps = ps;
                                strong = (uu___239_13711.strong)
                              }) env stack1 t2
                       | uu____13712 ->
                           let uu____13713 =
                             let uu____13714 =
                               let uu____13715 =
                                 let uu____13742 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13742, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13715 in
                             mk uu____13714 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13713))))
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
                         let uu____13852 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13852 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___240_13872 = cfg in
                               let uu____13873 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___240_13872.steps);
                                 tcenv = uu____13873;
                                 delta_level = (uu___240_13872.delta_level);
                                 primitive_steps =
                                   (uu___240_13872.primitive_steps);
                                 strong = (uu___240_13872.strong)
                               } in
                             let norm1 t2 =
                               let uu____13878 =
                                 let uu____13879 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13879 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13878 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___241_13882 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___241_13882.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___241_13882.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13883 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13883
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13894,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13895;
                               FStar_Syntax_Syntax.lbunivs = uu____13896;
                               FStar_Syntax_Syntax.lbtyp = uu____13897;
                               FStar_Syntax_Syntax.lbeff = uu____13898;
                               FStar_Syntax_Syntax.lbdef = uu____13899;_}::uu____13900),uu____13901)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13937 =
                 (let uu____13940 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13940) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13942 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13942))) in
               if uu____13937
               then
                 let binder =
                   let uu____13944 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13944 in
                 let env1 =
                   let uu____13954 =
                     let uu____13961 =
                       let uu____13962 =
                         let uu____13993 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13993,
                           false) in
                       Clos uu____13962 in
                     ((FStar_Pervasives_Native.Some binder), uu____13961) in
                   uu____13954 :: env in
                 (log cfg
                    (fun uu____14078  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____14080 =
                    let uu____14085 =
                      let uu____14086 =
                        let uu____14087 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14087
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14086] in
                    FStar_Syntax_Subst.open_term uu____14085 body in
                  match uu____14080 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____14096  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____14104 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____14104 in
                          FStar_Util.Inl
                            (let uu___242_14114 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___242_14114.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___242_14114.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____14117  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___243_14119 = lb in
                           let uu____14120 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___243_14119.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___243_14119.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____14120
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____14155  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___244_14175 = cfg in
                           {
                             steps = (uu___244_14175.steps);
                             tcenv = (uu___244_14175.tcenv);
                             delta_level = (uu___244_14175.delta_level);
                             primitive_steps =
                               (uu___244_14175.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____14178  ->
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
               let uu____14195 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14195 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14231 =
                               let uu___245_14232 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___245_14232.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___245_14232.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14231 in
                           let uu____14233 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14233 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14259 =
                                   FStar_List.map (fun uu____14275  -> dummy)
                                     lbs1 in
                                 let uu____14276 =
                                   let uu____14285 =
                                     FStar_List.map
                                       (fun uu____14305  -> dummy) xs1 in
                                   FStar_List.append uu____14285 env in
                                 FStar_List.append uu____14259 uu____14276 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14329 =
                                       let uu___246_14330 = rc in
                                       let uu____14331 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___246_14330.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14331;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___246_14330.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14329
                                 | uu____14338 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___247_14342 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___247_14342.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___247_14342.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14352 =
                        FStar_List.map (fun uu____14368  -> dummy) lbs2 in
                      FStar_List.append uu____14352 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14376 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14376 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___248_14392 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___248_14392.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___248_14392.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14419 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14419
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14438 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14514  ->
                        match uu____14514 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___249_14635 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___249_14635.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___249_14635.FStar_Syntax_Syntax.sort)
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
               (match uu____14438 with
                | (rec_env,memos,uu____14832) ->
                    let uu____14885 =
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
                             let uu____15416 =
                               let uu____15423 =
                                 let uu____15424 =
                                   let uu____15455 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15455, false) in
                                 Clos uu____15424 in
                               (FStar_Pervasives_Native.None, uu____15423) in
                             uu____15416 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15560 =
                      let uu____15561 = should_reify cfg stack in
                      Prims.op_Negation uu____15561 in
                    if uu____15560
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____15571 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15571
                        then
                          let uu___250_15572 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___250_15572.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___250_15572.primitive_steps);
                            strong = (uu___250_15572.strong)
                          }
                        else
                          (let uu___251_15574 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___251_15574.tcenv);
                             delta_level = (uu___251_15574.delta_level);
                             primitive_steps =
                               (uu___251_15574.primitive_steps);
                             strong = (uu___251_15574.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15576 =
                         let uu____15577 = FStar_Syntax_Subst.compress head1 in
                         uu____15577.FStar_Syntax_Syntax.n in
                       match uu____15576 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15595 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15595 with
                            | (uu____15596,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15602 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15610 =
                                         let uu____15611 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15611.FStar_Syntax_Syntax.n in
                                       match uu____15610 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15617,uu____15618))
                                           ->
                                           let uu____15627 =
                                             let uu____15628 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15628.FStar_Syntax_Syntax.n in
                                           (match uu____15627 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15634,msrc,uu____15636))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15645 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15645
                                            | uu____15646 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15647 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15648 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15648 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___252_15653 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___252_15653.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___252_15653.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___252_15653.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15654 =
                                            FStar_List.tl stack in
                                          let uu____15655 =
                                            let uu____15656 =
                                              let uu____15659 =
                                                let uu____15660 =
                                                  let uu____15673 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15673) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15660 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15659 in
                                            uu____15656
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15654
                                            uu____15655
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15689 =
                                            let uu____15690 = is_return body in
                                            match uu____15690 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15694;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15695;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15700 -> false in
                                          if uu____15689
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
                                               let uu____15724 =
                                                 let uu____15727 =
                                                   let uu____15728 =
                                                     let uu____15745 =
                                                       let uu____15748 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15748] in
                                                     (uu____15745, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15728 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15727 in
                                               uu____15724
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15764 =
                                                 let uu____15765 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15765.FStar_Syntax_Syntax.n in
                                               match uu____15764 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15771::uu____15772::[])
                                                   ->
                                                   let uu____15779 =
                                                     let uu____15782 =
                                                       let uu____15783 =
                                                         let uu____15790 =
                                                           let uu____15793 =
                                                             let uu____15794
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15794 in
                                                           let uu____15795 =
                                                             let uu____15798
                                                               =
                                                               let uu____15799
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15799 in
                                                             [uu____15798] in
                                                           uu____15793 ::
                                                             uu____15795 in
                                                         (bind1, uu____15790) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15783 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15782 in
                                                   uu____15779
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15807 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15813 =
                                                 let uu____15816 =
                                                   let uu____15817 =
                                                     let uu____15832 =
                                                       let uu____15835 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15836 =
                                                         let uu____15839 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15840 =
                                                           let uu____15843 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15844 =
                                                             let uu____15847
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15848
                                                               =
                                                               let uu____15851
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15852
                                                                 =
                                                                 let uu____15855
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15855] in
                                                               uu____15851 ::
                                                                 uu____15852 in
                                                             uu____15847 ::
                                                               uu____15848 in
                                                           uu____15843 ::
                                                             uu____15844 in
                                                         uu____15839 ::
                                                           uu____15840 in
                                                       uu____15835 ::
                                                         uu____15836 in
                                                     (bind_inst, uu____15832) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15817 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15816 in
                                               uu____15813
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15863 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____15863 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15887 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15887 with
                            | (uu____15888,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15923 =
                                        let uu____15924 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15924.FStar_Syntax_Syntax.n in
                                      match uu____15923 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15930) -> t4
                                      | uu____15935 -> head2 in
                                    let uu____15936 =
                                      let uu____15937 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15937.FStar_Syntax_Syntax.n in
                                    match uu____15936 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15943 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15944 = maybe_extract_fv head2 in
                                  match uu____15944 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15954 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15954
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15959 =
                                          maybe_extract_fv head3 in
                                        match uu____15959 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15964 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15965 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15970 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15985 =
                                    match uu____15985 with
                                    | (e,q) ->
                                        let uu____15992 =
                                          let uu____15993 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15993.FStar_Syntax_Syntax.n in
                                        (match uu____15992 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____16008 -> false) in
                                  let uu____16009 =
                                    let uu____16010 =
                                      let uu____16017 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____16017 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____16010 in
                                  if uu____16009
                                  then
                                    let uu____16022 =
                                      let uu____16023 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____16023 in
                                    failwith uu____16022
                                  else ());
                                 (let uu____16025 =
                                    maybe_unfold_action head_app in
                                  match uu____16025 with
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
                                      let uu____16064 = FStar_List.tl stack in
                                      norm cfg env uu____16064 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16078 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16078 in
                           let uu____16079 = FStar_List.tl stack in
                           norm cfg env uu____16079 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16200  ->
                                     match uu____16200 with
                                     | (pat,wopt,tm) ->
                                         let uu____16248 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16248))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16280 = FStar_List.tl stack in
                           norm cfg env uu____16280 tm
                       | uu____16281 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16289 = should_reify cfg stack in
                    if uu____16289
                    then
                      let uu____16290 = FStar_List.tl stack in
                      let uu____16291 =
                        let uu____16292 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16292 in
                      norm cfg env uu____16290 uu____16291
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16295 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16295
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___253_16304 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___253_16304.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___253_16304.primitive_steps);
                             strong = (uu___253_16304.strong)
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
                | uu____16306 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____16308::uu____16309 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16314) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16315 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____16346 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16360 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16360
                             | uu____16371 -> m in
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
              let uu____16383 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16383 in
            let uu____16384 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16384 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16397  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16408  ->
                      let uu____16409 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16410 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16409
                        uu____16410);
                 (let t1 =
                    let uu____16412 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16412
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
                    | (UnivArgs (us',uu____16422))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____16477 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____16480 ->
                        let uu____16483 =
                          let uu____16484 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16484 in
                        failwith uu____16483
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
              let uu____16494 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16494 with
              | (uu____16495,return_repr) ->
                  let return_inst =
                    let uu____16504 =
                      let uu____16505 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16505.FStar_Syntax_Syntax.n in
                    match uu____16504 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16511::[]) ->
                        let uu____16518 =
                          let uu____16521 =
                            let uu____16522 =
                              let uu____16529 =
                                let uu____16532 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16532] in
                              (return_tm, uu____16529) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16522 in
                          FStar_Syntax_Syntax.mk uu____16521 in
                        uu____16518 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16540 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16543 =
                    let uu____16546 =
                      let uu____16547 =
                        let uu____16562 =
                          let uu____16565 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16566 =
                            let uu____16569 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16569] in
                          uu____16565 :: uu____16566 in
                        (return_inst, uu____16562) in
                      FStar_Syntax_Syntax.Tm_app uu____16547 in
                    FStar_Syntax_Syntax.mk uu____16546 in
                  uu____16543 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16578 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16578 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16581 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16581
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16582;
                     FStar_TypeChecker_Env.mtarget = uu____16583;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16584;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16599;
                     FStar_TypeChecker_Env.mtarget = uu____16600;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16601;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16625 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16626 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16625 t FStar_Syntax_Syntax.tun uu____16626)
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
                (fun uu____16682  ->
                   match uu____16682 with
                   | (a,imp) ->
                       let uu____16693 = norm cfg env [] a in
                       (uu____16693, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___254_16710 = comp1 in
            let uu____16713 =
              let uu____16714 =
                let uu____16723 = norm cfg env [] t in
                let uu____16724 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16723, uu____16724) in
              FStar_Syntax_Syntax.Total uu____16714 in
            {
              FStar_Syntax_Syntax.n = uu____16713;
              FStar_Syntax_Syntax.pos =
                (uu___254_16710.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___254_16710.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___255_16739 = comp1 in
            let uu____16742 =
              let uu____16743 =
                let uu____16752 = norm cfg env [] t in
                let uu____16753 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16752, uu____16753) in
              FStar_Syntax_Syntax.GTotal uu____16743 in
            {
              FStar_Syntax_Syntax.n = uu____16742;
              FStar_Syntax_Syntax.pos =
                (uu___255_16739.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___255_16739.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16805  ->
                      match uu____16805 with
                      | (a,i) ->
                          let uu____16816 = norm cfg env [] a in
                          (uu____16816, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___201_16827  ->
                      match uu___201_16827 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16831 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16831
                      | f -> f)) in
            let uu___256_16835 = comp1 in
            let uu____16838 =
              let uu____16839 =
                let uu___257_16840 = ct in
                let uu____16841 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16842 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16845 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16841;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___257_16840.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16842;
                  FStar_Syntax_Syntax.effect_args = uu____16845;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16839 in
            {
              FStar_Syntax_Syntax.n = uu____16838;
              FStar_Syntax_Syntax.pos =
                (uu___256_16835.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___256_16835.FStar_Syntax_Syntax.vars)
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
            (let uu___258_16863 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___258_16863.tcenv);
               delta_level = (uu___258_16863.delta_level);
               primitive_steps = (uu___258_16863.primitive_steps);
               strong = (uu___258_16863.strong)
             }) env [] t in
        let non_info t =
          let uu____16868 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16868 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16871 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___259_16890 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___259_16890.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___259_16890.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16897 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16897
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
                    let uu___260_16908 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___260_16908.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___260_16908.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___260_16908.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___261_16910 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___261_16910.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___261_16910.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___261_16910.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___261_16910.FStar_Syntax_Syntax.flags)
                    } in
              let uu___262_16911 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___262_16911.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___262_16911.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16913 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16916  ->
        match uu____16916 with
        | (x,imp) ->
            let uu____16919 =
              let uu___263_16920 = x in
              let uu____16921 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___263_16920.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___263_16920.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16921
              } in
            (uu____16919, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16927 =
          FStar_List.fold_left
            (fun uu____16945  ->
               fun b  ->
                 match uu____16945 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16927 with | (nbs,uu____16985) -> FStar_List.rev nbs
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
            let uu____17001 =
              let uu___264_17002 = rc in
              let uu____17003 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___264_17002.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17003;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___264_17002.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17001
        | uu____17010 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17023  ->
               let uu____17024 = FStar_Syntax_Print.tag_of_term t in
               let uu____17025 = FStar_Syntax_Print.term_to_string t in
               let uu____17026 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17033 =
                 let uu____17034 =
                   let uu____17037 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17037 in
                 stack_to_string uu____17034 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____17024 uu____17025 uu____17026 uu____17033);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____17066 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____17066
                 then
                   let time_now = FStar_Util.now () in
                   let uu____17068 =
                     let uu____17069 =
                       let uu____17070 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17070 in
                     FStar_Util.string_of_int uu____17069 in
                   let uu____17075 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17076 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17068 uu____17075 uu____17076
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___265_17094 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___265_17094.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___265_17094.strong)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____17135  ->
                     let uu____17136 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17136);
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
               let uu____17172 =
                 let uu___266_17173 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___266_17173.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___266_17173.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____17172
           | (Arg (Univ uu____17174,uu____17175,uu____17176))::uu____17177 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17180,uu____17181))::uu____17182 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____17198),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17251  ->
                     let uu____17252 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17252);
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
                  (let uu____17262 = FStar_ST.op_Bang m in
                   match uu____17262 with
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
                   | FStar_Pervasives_Native.Some (uu____17406,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17449 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17449
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17461  ->
                     let uu____17462 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17462);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17467 =
                   log cfg
                     (fun uu____17472  ->
                        let uu____17473 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17474 =
                          let uu____17475 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17492  ->
                                    match uu____17492 with
                                    | (p,uu____17502,uu____17503) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17475
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17473 uu____17474);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___202_17520  ->
                                match uu___202_17520 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17521 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___267_17525 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___267_17525.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___267_17525.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17557 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17578 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17638  ->
                                    fun uu____17639  ->
                                      match (uu____17638, uu____17639) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17730 = norm_pat env3 p1 in
                                          (match uu____17730 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17578 with
                           | (pats1,env3) ->
                               ((let uu___268_17812 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___268_17812.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___269_17831 = x in
                            let uu____17832 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___269_17831.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___269_17831.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17832
                            } in
                          ((let uu___270_17846 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___270_17846.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___271_17857 = x in
                            let uu____17858 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___271_17857.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___271_17857.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17858
                            } in
                          ((let uu___272_17872 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___272_17872.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___273_17888 = x in
                            let uu____17889 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___273_17888.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___273_17888.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17889
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___274_17896 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___274_17896.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17906 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17920 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17920 with
                                  | (p,wopt,e) ->
                                      let uu____17940 = norm_pat env1 p in
                                      (match uu____17940 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17965 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17965 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17971 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17971) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17981) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17986 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17987;
                         FStar_Syntax_Syntax.fv_delta = uu____17988;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17989;
                         FStar_Syntax_Syntax.fv_delta = uu____17990;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17991);_}
                       -> true
                   | uu____17998 -> false in
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
                   let uu____18143 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18143 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18230 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18269 ->
                                 let uu____18270 =
                                   let uu____18271 = is_cons head1 in
                                   Prims.op_Negation uu____18271 in
                                 FStar_Util.Inr uu____18270)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18296 =
                              let uu____18297 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18297.FStar_Syntax_Syntax.n in
                            (match uu____18296 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18315 ->
                                 let uu____18316 =
                                   let uu____18317 = is_cons head1 in
                                   Prims.op_Negation uu____18317 in
                                 FStar_Util.Inr uu____18316))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18386)::rest_a,(p1,uu____18389)::rest_p) ->
                       let uu____18433 = matches_pat t1 p1 in
                       (match uu____18433 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18482 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18588 = matches_pat scrutinee1 p1 in
                       (match uu____18588 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18628  ->
                                  let uu____18629 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18630 =
                                    let uu____18631 =
                                      FStar_List.map
                                        (fun uu____18641  ->
                                           match uu____18641 with
                                           | (uu____18646,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18631
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18629 uu____18630);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18677  ->
                                       match uu____18677 with
                                       | (bv,t1) ->
                                           let uu____18700 =
                                             let uu____18707 =
                                               let uu____18710 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18710 in
                                             let uu____18711 =
                                               let uu____18712 =
                                                 let uu____18743 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18743, false) in
                                               Clos uu____18712 in
                                             (uu____18707, uu____18711) in
                                           uu____18700 :: env2) env1 s in
                              let uu____18852 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18852))) in
                 let uu____18853 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18853
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___203_18874  ->
                match uu___203_18874 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18878 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18884 -> d in
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
            let uu___275_18909 = config s e in
            {
              steps = (uu___275_18909.steps);
              tcenv = (uu___275_18909.tcenv);
              delta_level = (uu___275_18909.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___275_18909.strong)
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
      fun t  -> let uu____18934 = config s e in norm_comp uu____18934 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18947 = config [] env in norm_universe uu____18947 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18960 = config [] env in ghost_to_pure_aux uu____18960 [] c
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
        let uu____18978 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18978 in
      let uu____18985 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18985
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___276_18987 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___276_18987.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___276_18987.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18990  ->
                    let uu____18991 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18991))
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
            ((let uu____19008 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19008);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19019 = config [AllowUnboundUniverses] env in
          norm_comp uu____19019 [] c
        with
        | e ->
            ((let uu____19032 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19032);
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
                   let uu____19069 =
                     let uu____19070 =
                       let uu____19077 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____19077) in
                     FStar_Syntax_Syntax.Tm_refine uu____19070 in
                   mk uu____19069 t01.FStar_Syntax_Syntax.pos
               | uu____19082 -> t2)
          | uu____19083 -> t2 in
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
        let uu____19123 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19123 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19152 ->
                 let uu____19159 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19159 with
                  | (actuals,uu____19169,uu____19170) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19184 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19184 with
                         | (binders,args) ->
                             let uu____19201 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19201
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
      | uu____19209 ->
          let uu____19210 = FStar_Syntax_Util.head_and_args t in
          (match uu____19210 with
           | (head1,args) ->
               let uu____19247 =
                 let uu____19248 = FStar_Syntax_Subst.compress head1 in
                 uu____19248.FStar_Syntax_Syntax.n in
               (match uu____19247 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19251,thead) ->
                    let uu____19277 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19277 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19319 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___281_19327 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___281_19327.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___281_19327.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___281_19327.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___281_19327.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___281_19327.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___281_19327.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___281_19327.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___281_19327.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___281_19327.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___281_19327.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___281_19327.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___281_19327.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___281_19327.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___281_19327.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___281_19327.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___281_19327.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___281_19327.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___281_19327.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___281_19327.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___281_19327.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___281_19327.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___281_19327.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___281_19327.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___281_19327.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___281_19327.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___281_19327.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___281_19327.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___281_19327.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___281_19327.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___281_19327.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___281_19327.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19319 with
                            | (uu____19328,ty,uu____19330) ->
                                eta_expand_with_type env t ty))
                | uu____19331 ->
                    let uu____19332 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___282_19340 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___282_19340.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___282_19340.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___282_19340.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___282_19340.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___282_19340.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___282_19340.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___282_19340.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___282_19340.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___282_19340.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___282_19340.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___282_19340.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___282_19340.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___282_19340.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___282_19340.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___282_19340.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___282_19340.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___282_19340.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___282_19340.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___282_19340.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___282_19340.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___282_19340.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___282_19340.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___282_19340.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___282_19340.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___282_19340.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___282_19340.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___282_19340.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___282_19340.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___282_19340.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___282_19340.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___282_19340.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19332 with
                     | (uu____19341,ty,uu____19343) ->
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
            | (uu____19417,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19423,FStar_Util.Inl t) ->
                let uu____19429 =
                  let uu____19432 =
                    let uu____19433 =
                      let uu____19446 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19446) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19433 in
                  FStar_Syntax_Syntax.mk uu____19432 in
                uu____19429 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19450 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19450 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19477 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19532 ->
                    let uu____19533 =
                      let uu____19542 =
                        let uu____19543 = FStar_Syntax_Subst.compress t3 in
                        uu____19543.FStar_Syntax_Syntax.n in
                      (uu____19542, tc) in
                    (match uu____19533 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19568) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19605) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19644,FStar_Util.Inl uu____19645) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19668 -> failwith "Impossible") in
              (match uu____19477 with
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
          let uu____19773 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19773 with
          | (univ_names1,binders1,tc) ->
              let uu____19831 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19831)
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
          let uu____19866 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19866 with
          | (univ_names1,binders1,tc) ->
              let uu____19926 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19926)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19959 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19959 with
           | (univ_names1,binders1,typ1) ->
               let uu___283_19987 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_19987.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_19987.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_19987.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_19987.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___284_20008 = s in
          let uu____20009 =
            let uu____20010 =
              let uu____20019 = FStar_List.map (elim_uvars env) sigs in
              (uu____20019, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20010 in
          {
            FStar_Syntax_Syntax.sigel = uu____20009;
            FStar_Syntax_Syntax.sigrng =
              (uu___284_20008.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___284_20008.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___284_20008.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___284_20008.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20036 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20036 with
           | (univ_names1,uu____20054,typ1) ->
               let uu___285_20068 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___285_20068.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___285_20068.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___285_20068.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___285_20068.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20074 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20074 with
           | (univ_names1,uu____20092,typ1) ->
               let uu___286_20106 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___286_20106.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___286_20106.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___286_20106.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___286_20106.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20140 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20140 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20163 =
                            let uu____20164 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20164 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20163 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___287_20167 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___287_20167.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___287_20167.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___288_20168 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___288_20168.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___288_20168.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___288_20168.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___288_20168.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___289_20180 = s in
          let uu____20181 =
            let uu____20182 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20182 in
          {
            FStar_Syntax_Syntax.sigel = uu____20181;
            FStar_Syntax_Syntax.sigrng =
              (uu___289_20180.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___289_20180.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___289_20180.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___289_20180.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20186 = elim_uvars_aux_t env us [] t in
          (match uu____20186 with
           | (us1,uu____20204,t1) ->
               let uu___290_20218 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___290_20218.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___290_20218.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___290_20218.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___290_20218.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20219 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20221 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20221 with
           | (univs1,binders,signature) ->
               let uu____20249 =
                 let uu____20258 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20258 with
                 | (univs_opening,univs2) ->
                     let uu____20285 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20285) in
               (match uu____20249 with
                | (univs_opening,univs_closing) ->
                    let uu____20302 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20308 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20309 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20308, uu____20309) in
                    (match uu____20302 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20331 =
                           match uu____20331 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20349 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20349 with
                                | (us1,t1) ->
                                    let uu____20360 =
                                      let uu____20365 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20372 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20365, uu____20372) in
                                    (match uu____20360 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20385 =
                                           let uu____20390 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20399 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20390, uu____20399) in
                                         (match uu____20385 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20415 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20415 in
                                              let uu____20416 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20416 with
                                               | (uu____20437,uu____20438,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20453 =
                                                       let uu____20454 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20454 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20453 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20459 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20459 with
                           | (uu____20472,uu____20473,t1) -> t1 in
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
                             | uu____20533 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20550 =
                               let uu____20551 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20551.FStar_Syntax_Syntax.n in
                             match uu____20550 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20610 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20639 =
                               let uu____20640 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20640.FStar_Syntax_Syntax.n in
                             match uu____20639 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20661) ->
                                 let uu____20682 = destruct_action_body body in
                                 (match uu____20682 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20727 ->
                                 let uu____20728 = destruct_action_body t in
                                 (match uu____20728 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20777 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20777 with
                           | (action_univs,t) ->
                               let uu____20786 = destruct_action_typ_templ t in
                               (match uu____20786 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___291_20827 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___291_20827.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___291_20827.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___292_20829 = ed in
                           let uu____20830 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20831 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20832 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20833 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20838 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20839 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20840 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20841 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20843 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___292_20829.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___292_20829.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20830;
                             FStar_Syntax_Syntax.bind_wp = uu____20831;
                             FStar_Syntax_Syntax.if_then_else = uu____20832;
                             FStar_Syntax_Syntax.ite_wp = uu____20833;
                             FStar_Syntax_Syntax.stronger = uu____20834;
                             FStar_Syntax_Syntax.close_wp = uu____20835;
                             FStar_Syntax_Syntax.assert_p = uu____20836;
                             FStar_Syntax_Syntax.assume_p = uu____20837;
                             FStar_Syntax_Syntax.null_wp = uu____20838;
                             FStar_Syntax_Syntax.trivial = uu____20839;
                             FStar_Syntax_Syntax.repr = uu____20840;
                             FStar_Syntax_Syntax.return_repr = uu____20841;
                             FStar_Syntax_Syntax.bind_repr = uu____20842;
                             FStar_Syntax_Syntax.actions = uu____20843
                           } in
                         let uu___293_20846 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___293_20846.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___293_20846.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___293_20846.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___293_20846.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___204_20863 =
            match uu___204_20863 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20890 = elim_uvars_aux_t env us [] t in
                (match uu____20890 with
                 | (us1,uu____20914,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___294_20933 = sub_eff in
            let uu____20934 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20937 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___294_20933.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___294_20933.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20934;
              FStar_Syntax_Syntax.lift = uu____20937
            } in
          let uu___295_20940 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___295_20940.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___295_20940.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___295_20940.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___295_20940.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20950 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20950 with
           | (univ_names1,binders1,comp1) ->
               let uu___296_20984 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___296_20984.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___296_20984.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___296_20984.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___296_20984.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20995 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t