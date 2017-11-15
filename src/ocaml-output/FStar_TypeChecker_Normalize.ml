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
let built_in_primitive_steps:
  FStar_TypeChecker_Env.env -> primitive_step Prims.list =
  fun env  ->
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
      let uu____4056 = FStar_Syntax_Embeddings.unembed_list_safe u in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4056 in
    let arg_as_bounded_int uu____4084 =
      match uu____4084 with
      | (a,uu____4096) ->
          let uu____4103 =
            let uu____4104 = FStar_Syntax_Subst.compress a in
            uu____4104.FStar_Syntax_Syntax.n in
          (match uu____4103 with
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                  FStar_Syntax_Syntax.pos = uu____4114;
                  FStar_Syntax_Syntax.vars = uu____4115;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_constant
                                                                (FStar_Const.Const_int
                                                                (i,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____4117;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____4118;_},uu____4119)::[])
               when
               FStar_Util.ends_with
                 (FStar_Ident.text_of_lid
                    (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                 "int_to_t"
               ->
               let uu____4158 =
                 let uu____4163 = FStar_BigInt.big_int_of_string i in
                 (fv1, uu____4163) in
               FStar_Pervasives_Native.Some uu____4158
           | uu____4168 -> FStar_Pervasives_Native.None) in
    let lift_unary f aopts =
      match aopts with
      | (FStar_Pervasives_Native.Some a)::[] ->
          let uu____4210 = f a in FStar_Pervasives_Native.Some uu____4210
      | uu____4211 -> FStar_Pervasives_Native.None in
    let lift_binary f aopts =
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu____4261 = f a0 a1 in FStar_Pervasives_Native.Some uu____4261
      | uu____4262 -> FStar_Pervasives_Native.None in
    let unary_op as_a f res args =
      let uu____4311 = FStar_List.map as_a args in
      lift_unary (f res.psc_range) uu____4311 in
    let binary_op as_a f res args =
      let uu____4367 = FStar_List.map as_a args in
      lift_binary (f res.psc_range) uu____4367 in
    let as_primitive_step uu____4391 =
      match uu____4391 with
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
             let uu____4439 = f x in
             FStar_Syntax_Embeddings.embed_int r uu____4439) in
    let binary_int_op f =
      binary_op arg_as_int
        (fun r  ->
           fun x  ->
             fun y  ->
               let uu____4467 = f x y in
               FStar_Syntax_Embeddings.embed_int r uu____4467) in
    let unary_bool_op f =
      unary_op arg_as_bool
        (fun r  ->
           fun x  ->
             let uu____4488 = f x in
             FStar_Syntax_Embeddings.embed_bool r uu____4488) in
    let binary_bool_op f =
      binary_op arg_as_bool
        (fun r  ->
           fun x  ->
             fun y  ->
               let uu____4516 = f x y in
               FStar_Syntax_Embeddings.embed_bool r uu____4516) in
    let binary_string_op f =
      binary_op arg_as_string
        (fun r  ->
           fun x  ->
             fun y  ->
               let uu____4544 = f x y in
               FStar_Syntax_Embeddings.embed_string r uu____4544) in
    let list_of_string' rng s =
      let char_t =
        let uu____4553 =
          let uu____4558 =
            FStar_ToSyntax_Env.try_lookup_lid env.FStar_TypeChecker_Env.dsenv
              FStar_Parser_Const.char_lid in
          FStar_All.pipe_right uu____4558 FStar_Util.must in
        FStar_All.pipe_right uu____4553 FStar_Pervasives_Native.fst in
      let charterm c =
        mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
      let uu____4589 =
        let uu____4592 = FStar_String.list_of_string s in
        FStar_List.map charterm uu____4592 in
      FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4589 in
    let string_of_list' rng l =
      let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
    let string_compare' rng s1 s2 =
      let r = FStar_String.compare s1 s2 in
      let uu____4624 =
        let uu____4625 = FStar_Util.string_of_int r in
        FStar_BigInt.big_int_of_string uu____4625 in
      FStar_Syntax_Embeddings.embed_int rng uu____4624 in
    let string_concat' psc args =
      match args with
      | a1::a2::[] ->
          let uu____4643 = arg_as_string a1 in
          (match uu____4643 with
           | FStar_Pervasives_Native.Some s1 ->
               let uu____4649 =
                 arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
               (match uu____4649 with
                | FStar_Pervasives_Native.Some s2 ->
                    let r = FStar_String.concat s1 s2 in
                    let uu____4662 =
                      FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                    FStar_Pervasives_Native.Some uu____4662
                | uu____4663 -> FStar_Pervasives_Native.None)
           | uu____4668 -> FStar_Pervasives_Native.None)
      | uu____4671 -> FStar_Pervasives_Native.None in
    let string_of_int1 rng i =
      let uu____4681 = FStar_BigInt.string_of_big_int i in
      FStar_Syntax_Embeddings.embed_string rng uu____4681 in
    let string_of_bool1 rng b =
      FStar_Syntax_Embeddings.embed_string rng
        (if b then "true" else "false") in
    let term_of_range r =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
        FStar_Pervasives_Native.None r in
    let mk_range1 uu____4705 args =
      match args with
      | fn::from_line::from_col::to_line::to_col::[] ->
          let uu____4716 =
            let uu____4737 = arg_as_string fn in
            let uu____4740 = arg_as_int from_line in
            let uu____4743 = arg_as_int from_col in
            let uu____4746 = arg_as_int to_line in
            let uu____4749 = arg_as_int to_col in
            (uu____4737, uu____4740, uu____4743, uu____4746, uu____4749) in
          (match uu____4716 with
           | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
              from_l,FStar_Pervasives_Native.Some
              from_c,FStar_Pervasives_Native.Some
              to_l,FStar_Pervasives_Native.Some to_c) ->
               let r =
                 let uu____4780 =
                   let uu____4781 = FStar_BigInt.to_int_fs from_l in
                   let uu____4782 = FStar_BigInt.to_int_fs from_c in
                   FStar_Range.mk_pos uu____4781 uu____4782 in
                 let uu____4783 =
                   let uu____4784 = FStar_BigInt.to_int_fs to_l in
                   let uu____4785 = FStar_BigInt.to_int_fs to_c in
                   FStar_Range.mk_pos uu____4784 uu____4785 in
                 FStar_Range.mk_range fn1 uu____4780 uu____4783 in
               let uu____4786 = term_of_range r in
               FStar_Pervasives_Native.Some uu____4786
           | uu____4791 -> FStar_Pervasives_Native.None)
      | uu____4812 -> FStar_Pervasives_Native.None in
    let decidable_eq neg psc args =
      let r = psc.psc_range in
      let tru =
        mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
      let fal =
        mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
      match args with
      | (_typ,uu____4839)::(a1,uu____4841)::(a2,uu____4843)::[] ->
          let uu____4880 = FStar_Syntax_Util.eq_tm a1 a2 in
          (match uu____4880 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4893 -> FStar_Pervasives_Native.None)
      | uu____4894 -> failwith "Unexpected number of arguments" in
    let idstep psc args =
      match args with
      | (a1,uu____4921)::[] -> FStar_Pervasives_Native.Some a1
      | uu____4930 -> failwith "Unexpected number of arguments" in
    let basic_ops =
      let uu____4954 =
        let uu____4969 =
          let uu____4984 =
            let uu____4999 =
              let uu____5014 =
                let uu____5029 =
                  let uu____5044 =
                    let uu____5059 =
                      let uu____5074 =
                        let uu____5089 =
                          let uu____5104 =
                            let uu____5119 =
                              let uu____5134 =
                                let uu____5149 =
                                  let uu____5164 =
                                    let uu____5179 =
                                      let uu____5194 =
                                        let uu____5209 =
                                          let uu____5224 =
                                            let uu____5239 =
                                              let uu____5252 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5252,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5259 =
                                              let uu____5274 =
                                                let uu____5287 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5287,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5298 =
                                                let uu____5313 =
                                                  let uu____5328 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5328,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5337 =
                                                  let uu____5354 =
                                                    let uu____5369 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5369,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5378 =
                                                    let uu____5395 =
                                                      let uu____5414 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5414,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5395] in
                                                  uu____5354 :: uu____5378 in
                                                uu____5313 :: uu____5337 in
                                              uu____5274 :: uu____5298 in
                                            uu____5239 :: uu____5259 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5224 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5209 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5194 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5179 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5164 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5149 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5134 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5119 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5104 in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"),
                          (binary_int_op
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)))
                          :: uu____5089 in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (binary_op arg_as_int
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____5750 =
                                    FStar_BigInt.ge_big_int x y in
                                  FStar_Syntax_Embeddings.embed_bool r
                                    uu____5750)))
                        :: uu____5074 in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5776 = FStar_BigInt.gt_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5776)))
                      :: uu____5059 in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5802 = FStar_BigInt.le_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5802)))
                    :: uu____5044 in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5828 = FStar_BigInt.lt_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5828)))
                  :: uu____5029 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (binary_int_op
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
                :: uu____5014 in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
              :: uu____4999 in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
            :: uu____4984 in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
          :: uu____4969 in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) ::
        uu____4954 in
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
        let uu____5978 =
          let uu____5979 =
            let uu____5980 = FStar_Syntax_Syntax.as_arg c in [uu____5980] in
          FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5979 in
        uu____5978 FStar_Pervasives_Native.None r in
      FStar_All.pipe_right bounded_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6015 =
                let uu____6028 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____6028, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6048  ->
                          fun uu____6049  ->
                            match (uu____6048, uu____6049) with
                            | ((int_to_t1,x),(uu____6068,y)) ->
                                let uu____6078 = FStar_BigInt.add_big_int x y in
                                int_as_bounded r int_to_t1 uu____6078))) in
              let uu____6079 =
                let uu____6094 =
                  let uu____6107 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____6107, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6127  ->
                            fun uu____6128  ->
                              match (uu____6127, uu____6128) with
                              | ((int_to_t1,x),(uu____6147,y)) ->
                                  let uu____6157 =
                                    FStar_BigInt.sub_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6157))) in
                let uu____6158 =
                  let uu____6173 =
                    let uu____6186 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____6186, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____6206  ->
                              fun uu____6207  ->
                                match (uu____6206, uu____6207) with
                                | ((int_to_t1,x),(uu____6226,y)) ->
                                    let uu____6236 =
                                      FStar_BigInt.mult_big_int x y in
                                    int_as_bounded r int_to_t1 uu____6236))) in
                  [uu____6173] in
                uu____6094 :: uu____6158 in
              uu____6015 :: uu____6079)) in
    FStar_List.map as_primitive_step
      (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6326)::(a1,uu____6328)::(a2,uu____6330)::[] ->
        let uu____6367 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6367 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_6373 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_6373.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_6373.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6377 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6377.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6377.FStar_Syntax_Syntax.vars)
                })
         | uu____6378 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6380)::uu____6381::(a1,uu____6383)::(a2,uu____6385)::[] ->
        let uu____6434 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6434 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_6440 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_6440.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_6440.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6444 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6444.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6444.FStar_Syntax_Syntax.vars)
                })
         | uu____6445 -> FStar_Pervasives_Native.None)
    | uu____6446 -> failwith "Unexpected number of arguments" in
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
      let uu____6465 =
        let uu____6466 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6466 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6465
    with | uu____6472 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6476 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6476) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6536  ->
           fun subst1  ->
             match uu____6536 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6578)) ->
                      let uu____6637 = b in
                      (match uu____6637 with
                       | (bv,uu____6645) ->
                           let uu____6646 =
                             let uu____6647 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6647 in
                           if uu____6646
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6652 = unembed_binder term1 in
                              match uu____6652 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6659 =
                                      let uu___227_6660 = bv in
                                      let uu____6661 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___227_6660.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___227_6660.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6661
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6659 in
                                  let b_for_x =
                                    let uu____6665 =
                                      let uu____6672 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6672) in
                                    FStar_Syntax_Syntax.NT uu____6665 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___194_6681  ->
                                         match uu___194_6681 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6682,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6684;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6685;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6690 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6691 -> subst1)) env []
let reduce_primops:
  'Auu____6708 'Auu____6709 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6709) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6708 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6750 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6750
          then tm
          else
            (let uu____6752 = FStar_Syntax_Util.head_and_args tm in
             match uu____6752 with
             | (head1,args) ->
                 let uu____6789 =
                   let uu____6790 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6790.FStar_Syntax_Syntax.n in
                 (match uu____6789 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6794 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6794 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6811  ->
                                   let uu____6812 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6813 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6820 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6812 uu____6813 uu____6820);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6825  ->
                                   let uu____6826 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6826);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6829  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6831 =
                                 prim_step.interpretation psc args in
                               match uu____6831 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6837  ->
                                         let uu____6838 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6838);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6844  ->
                                         let uu____6845 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6846 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6845 uu____6846);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6847 ->
                           (log_primops cfg
                              (fun uu____6851  ->
                                 let uu____6852 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6852);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6856  ->
                            let uu____6857 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6857);
                       (match args with
                        | (a1,uu____6859)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6876 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6888  ->
                            let uu____6889 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6889);
                       (match args with
                        | (a1,uu____6891)::(a2,uu____6893)::[] ->
                            let uu____6920 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____6920 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___228_6924 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___228_6924.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___228_6924.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6927 -> tm))
                  | uu____6936 -> tm))
let reduce_equality:
  'Auu____6941 'Auu____6942 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6942) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6941 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___229_6980 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___229_6980.tcenv);
           delta_level = (uu___229_6980.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___229_6980.strong)
         }) tm
let maybe_simplify:
  'Auu____6987 'Auu____6988 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6988) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6987 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7030 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7030
          then tm1
          else
            (let w t =
               let uu___230_7042 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___230_7042.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___230_7042.FStar_Syntax_Syntax.vars)
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
               | uu____7059 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7099;
                         FStar_Syntax_Syntax.vars = uu____7100;_},uu____7101);
                    FStar_Syntax_Syntax.pos = uu____7102;
                    FStar_Syntax_Syntax.vars = uu____7103;_},args)
                 ->
                 let uu____7129 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7129
                 then
                   let uu____7130 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7130 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7185)::
                        (uu____7186,(arg,uu____7188))::[] -> arg
                    | (uu____7253,(arg,uu____7255))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7256)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7321)::uu____7322::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7385::(FStar_Pervasives_Native.Some (false
                                   ),uu____7386)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7449 -> tm1)
                 else
                   (let uu____7465 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7465
                    then
                      let uu____7466 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7466 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7521)::uu____7522::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7585::(FStar_Pervasives_Native.Some (true
                                     ),uu____7586)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7649)::
                          (uu____7650,(arg,uu____7652))::[] -> arg
                      | (uu____7717,(arg,uu____7719))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7720)::[]
                          -> arg
                      | uu____7785 -> tm1
                    else
                      (let uu____7801 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7801
                       then
                         let uu____7802 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7802 with
                         | uu____7857::(FStar_Pervasives_Native.Some (true
                                        ),uu____7858)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____7921)::uu____7922::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____7985)::
                             (uu____7986,(arg,uu____7988))::[] -> arg
                         | (uu____8053,(p,uu____8055))::(uu____8056,(q,uu____8058))::[]
                             ->
                             let uu____8123 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8123
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8125 -> tm1
                       else
                         (let uu____8141 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8141
                          then
                            let uu____8142 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8142 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8197)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8236)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8275 -> tm1
                          else
                            (let uu____8291 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8291
                             then
                               match args with
                               | (t,uu____8293)::[] ->
                                   let uu____8310 =
                                     let uu____8311 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8311.FStar_Syntax_Syntax.n in
                                   (match uu____8310 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8314::[],body,uu____8316) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8343 -> tm1)
                                    | uu____8346 -> tm1)
                               | (uu____8347,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8348))::
                                   (t,uu____8350)::[] ->
                                   let uu____8389 =
                                     let uu____8390 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8390.FStar_Syntax_Syntax.n in
                                   (match uu____8389 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8393::[],body,uu____8395) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8422 -> tm1)
                                    | uu____8425 -> tm1)
                               | uu____8426 -> tm1
                             else
                               (let uu____8436 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8436
                                then
                                  match args with
                                  | (t,uu____8438)::[] ->
                                      let uu____8455 =
                                        let uu____8456 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8456.FStar_Syntax_Syntax.n in
                                      (match uu____8455 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8459::[],body,uu____8461)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8488 -> tm1)
                                       | uu____8491 -> tm1)
                                  | (uu____8492,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8493))::(t,uu____8495)::[] ->
                                      let uu____8534 =
                                        let uu____8535 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8535.FStar_Syntax_Syntax.n in
                                      (match uu____8534 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8538::[],body,uu____8540)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8567 -> tm1)
                                       | uu____8570 -> tm1)
                                  | uu____8571 -> tm1
                                else
                                  (let uu____8581 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8581
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8582;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8583;_},uu____8584)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8601;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8602;_},uu____8603)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8620 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8631;
                    FStar_Syntax_Syntax.vars = uu____8632;_},args)
                 ->
                 let uu____8654 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8654
                 then
                   let uu____8655 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8655 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8710)::
                        (uu____8711,(arg,uu____8713))::[] -> arg
                    | (uu____8778,(arg,uu____8780))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8781)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8846)::uu____8847::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8910::(FStar_Pervasives_Native.Some (false
                                   ),uu____8911)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8974 -> tm1)
                 else
                   (let uu____8990 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8990
                    then
                      let uu____8991 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8991 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9046)::uu____9047::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9110::(FStar_Pervasives_Native.Some (true
                                     ),uu____9111)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9174)::
                          (uu____9175,(arg,uu____9177))::[] -> arg
                      | (uu____9242,(arg,uu____9244))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9245)::[]
                          -> arg
                      | uu____9310 -> tm1
                    else
                      (let uu____9326 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9326
                       then
                         let uu____9327 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9327 with
                         | uu____9382::(FStar_Pervasives_Native.Some (true
                                        ),uu____9383)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9446)::uu____9447::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9510)::
                             (uu____9511,(arg,uu____9513))::[] -> arg
                         | (uu____9578,(p,uu____9580))::(uu____9581,(q,uu____9583))::[]
                             ->
                             let uu____9648 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9648
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9650 -> tm1
                       else
                         (let uu____9666 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9666
                          then
                            let uu____9667 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9667 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9722)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9761)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9800 -> tm1
                          else
                            (let uu____9816 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9816
                             then
                               match args with
                               | (t,uu____9818)::[] ->
                                   let uu____9835 =
                                     let uu____9836 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9836.FStar_Syntax_Syntax.n in
                                   (match uu____9835 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9839::[],body,uu____9841) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9868 -> tm1)
                                    | uu____9871 -> tm1)
                               | (uu____9872,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9873))::
                                   (t,uu____9875)::[] ->
                                   let uu____9914 =
                                     let uu____9915 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9915.FStar_Syntax_Syntax.n in
                                   (match uu____9914 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9918::[],body,uu____9920) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9947 -> tm1)
                                    | uu____9950 -> tm1)
                               | uu____9951 -> tm1
                             else
                               (let uu____9961 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9961
                                then
                                  match args with
                                  | (t,uu____9963)::[] ->
                                      let uu____9980 =
                                        let uu____9981 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9981.FStar_Syntax_Syntax.n in
                                      (match uu____9980 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9984::[],body,uu____9986)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10013 -> tm1)
                                       | uu____10016 -> tm1)
                                  | (uu____10017,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10018))::(t,uu____10020)::[] ->
                                      let uu____10059 =
                                        let uu____10060 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10060.FStar_Syntax_Syntax.n in
                                      (match uu____10059 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10063::[],body,uu____10065)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10092 -> tm1)
                                       | uu____10095 -> tm1)
                                  | uu____10096 -> tm1
                                else
                                  (let uu____10106 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10106
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10107;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10108;_},uu____10109)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10126;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10127;_},uu____10128)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10145 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | uu____10155 -> tm1)
let is_norm_request:
  'Auu____10159 .
    FStar_Syntax_Syntax.term -> 'Auu____10159 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10172 =
        let uu____10179 =
          let uu____10180 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10180.FStar_Syntax_Syntax.n in
        (uu____10179, args) in
      match uu____10172 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10186::uu____10187::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10191::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10196::uu____10197::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10200 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___195_10211  ->
    match uu___195_10211 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10217 =
          let uu____10220 =
            let uu____10221 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10221 in
          [uu____10220] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10217
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10236 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10236) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10274 =
          let uu____10277 =
            let uu____10282 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10282 s in
          FStar_All.pipe_right uu____10277 FStar_Util.must in
        FStar_All.pipe_right uu____10274 tr_norm_steps in
      match args with
      | uu____10307::(tm,uu____10309)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10332)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10347)::uu____10348::(tm,uu____10350)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10390 =
              let uu____10393 = full_norm steps in parse_steps uu____10393 in
            Beta :: uu____10390 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10402 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___196_10419  ->
    match uu___196_10419 with
    | (App
        (uu____10422,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10423;
                       FStar_Syntax_Syntax.vars = uu____10424;_},uu____10425,uu____10426))::uu____10427
        -> true
    | uu____10434 -> false
let firstn:
  'Auu____10440 .
    Prims.int ->
      'Auu____10440 Prims.list ->
        ('Auu____10440 Prims.list,'Auu____10440 Prims.list)
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
          (uu____10476,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10477;
                         FStar_Syntax_Syntax.vars = uu____10478;_},uu____10479,uu____10480))::uu____10481
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10488 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10604  ->
               let uu____10605 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10606 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10607 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10614 =
                 let uu____10615 =
                   let uu____10618 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10618 in
                 stack_to_string uu____10615 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10605 uu____10606 uu____10607 uu____10614);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10641 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10666 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10683 =
                 let uu____10684 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10685 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10684 uu____10685 in
               failwith uu____10683
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10686 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10703 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10704 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10705;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10706;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10709;
                 FStar_Syntax_Syntax.fv_delta = uu____10710;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10711;
                 FStar_Syntax_Syntax.fv_delta = uu____10712;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10713);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10721 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10721 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____10727  ->
                     let uu____10728 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10729 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10728 uu____10729);
                if b
                then
                  (let uu____10730 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____10730 t1 fv)
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
                 let uu___231_10769 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___231_10769.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___231_10769.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10802 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10802) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___232_10810 = cfg in
                 let uu____10811 =
                   FStar_List.filter
                     (fun uu___197_10814  ->
                        match uu___197_10814 with
                        | UnfoldOnly uu____10815 -> false
                        | NoDeltaSteps  -> false
                        | uu____10818 -> true) cfg.steps in
                 {
                   steps = uu____10811;
                   tcenv = (uu___232_10810.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___232_10810.primitive_steps);
                   strong = (uu___232_10810.strong)
                 } in
               let uu____10819 = get_norm_request (norm cfg' env []) args in
               (match uu____10819 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10835 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___198_10840  ->
                                match uu___198_10840 with
                                | UnfoldUntil uu____10841 -> true
                                | UnfoldOnly uu____10842 -> true
                                | uu____10845 -> false)) in
                      if uu____10835
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___233_10850 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___233_10850.tcenv);
                        delta_level;
                        primitive_steps = (uu___233_10850.primitive_steps);
                        strong = (uu___233_10850.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____10861 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10861
                      then
                        let uu____10864 =
                          let uu____10865 =
                            let uu____10870 = FStar_Util.now () in
                            (t1, uu____10870) in
                          Debug uu____10865 in
                        uu____10864 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____10872;
                  FStar_Syntax_Syntax.vars = uu____10873;_},a1::a2::rest)
               ->
               let uu____10921 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____10921 with
                | (hd1,uu____10937) ->
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
                  FStar_Syntax_Syntax.pos = uu____11002;
                  FStar_Syntax_Syntax.vars = uu____11003;_},a1::a2::rest)
               ->
               let uu____11051 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11051 with
                | (hd1,uu____11067) ->
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
                  FStar_Syntax_Syntax.pos = uu____11132;
                  FStar_Syntax_Syntax.vars = uu____11133;_},a1::a2::a3::rest)
               ->
               let uu____11194 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11194 with
                | (hd1,uu____11210) ->
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
                    (FStar_Const.Const_reflect uu____11281);
                  FStar_Syntax_Syntax.pos = uu____11282;
                  FStar_Syntax_Syntax.vars = uu____11283;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11315 = FStar_List.tl stack in
               norm cfg env uu____11315 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11318;
                  FStar_Syntax_Syntax.vars = uu____11319;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11351 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11351 with
                | (reify_head,uu____11367) ->
                    let a1 =
                      let uu____11389 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11389 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11392);
                            FStar_Syntax_Syntax.pos = uu____11393;
                            FStar_Syntax_Syntax.vars = uu____11394;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11428 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11438 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11438
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11445 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11445
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11448 =
                      let uu____11455 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11455, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11448 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___199_11468  ->
                         match uu___199_11468 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11471 =
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
                 if uu____11471
                 then false
                 else
                   (let uu____11473 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___200_11480  ->
                              match uu___200_11480 with
                              | UnfoldOnly uu____11481 -> true
                              | uu____11484 -> false)) in
                    match uu____11473 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11488 -> should_delta) in
               (log cfg
                  (fun uu____11496  ->
                     let uu____11497 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11498 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11499 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11497 uu____11498 uu____11499);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11502 = lookup_bvar env x in
               (match uu____11502 with
                | Univ uu____11505 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11554 = FStar_ST.op_Bang r in
                      (match uu____11554 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11691  ->
                                 let uu____11692 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11693 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11692
                                   uu____11693);
                            (let uu____11694 =
                               let uu____11695 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11695.FStar_Syntax_Syntax.n in
                             match uu____11694 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11698 ->
                                 norm cfg env2 stack t'
                             | uu____11715 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11773)::uu____11774 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11783)::uu____11784 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11794,uu____11795))::stack_rest ->
                    (match c with
                     | Univ uu____11799 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11808 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11829  ->
                                    let uu____11830 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11830);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11870  ->
                                    let uu____11871 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11871);
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
                      (let uu___234_11921 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___234_11921.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___234_11921.strong)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11954  ->
                          let uu____11955 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11955);
                     norm cfg env stack1 t1)
                | (Debug uu____11956)::uu____11957 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11964 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11964
                    else
                      (let uu____11966 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11966 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12008  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12036 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12036
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12046 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12046)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12051 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12051.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12051.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12052 -> lopt in
                           (log cfg
                              (fun uu____12058  ->
                                 let uu____12059 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12059);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12072 = cfg in
                               {
                                 steps = (uu___236_12072.steps);
                                 tcenv = (uu___236_12072.tcenv);
                                 delta_level = (uu___236_12072.delta_level);
                                 primitive_steps =
                                   (uu___236_12072.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12083)::uu____12084 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12091 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12091
                    else
                      (let uu____12093 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12093 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12135  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12163 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12163
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12173 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12173)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12178 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12178.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12178.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12179 -> lopt in
                           (log cfg
                              (fun uu____12185  ->
                                 let uu____12186 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12186);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12199 = cfg in
                               {
                                 steps = (uu___236_12199.steps);
                                 tcenv = (uu___236_12199.tcenv);
                                 delta_level = (uu___236_12199.delta_level);
                                 primitive_steps =
                                   (uu___236_12199.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12210)::uu____12211 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12222 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12222
                    else
                      (let uu____12224 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12224 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12266  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12294 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12294
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12304 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12304)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12309 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12309.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12309.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12310 -> lopt in
                           (log cfg
                              (fun uu____12316  ->
                                 let uu____12317 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12317);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12330 = cfg in
                               {
                                 steps = (uu___236_12330.steps);
                                 tcenv = (uu___236_12330.tcenv);
                                 delta_level = (uu___236_12330.delta_level);
                                 primitive_steps =
                                   (uu___236_12330.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12341)::uu____12342 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12353 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12353
                    else
                      (let uu____12355 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12355 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12397  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12425 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12425
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12435 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12435)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12440 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12440.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12440.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12441 -> lopt in
                           (log cfg
                              (fun uu____12447  ->
                                 let uu____12448 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12448);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12461 = cfg in
                               {
                                 steps = (uu___236_12461.steps);
                                 tcenv = (uu___236_12461.tcenv);
                                 delta_level = (uu___236_12461.delta_level);
                                 primitive_steps =
                                   (uu___236_12461.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12472)::uu____12473 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12488 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12488
                    else
                      (let uu____12490 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12490 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12532  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12560 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12560
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12570 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12570)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12575 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12575.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12575.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12576 -> lopt in
                           (log cfg
                              (fun uu____12582  ->
                                 let uu____12583 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12583);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12596 = cfg in
                               {
                                 steps = (uu___236_12596.steps);
                                 tcenv = (uu___236_12596.tcenv);
                                 delta_level = (uu___236_12596.delta_level);
                                 primitive_steps =
                                   (uu___236_12596.primitive_steps);
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
                      let uu____12607 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12607
                    else
                      (let uu____12609 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12609 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12651  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12679 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12679
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12689 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12689)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12694 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12694.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12694.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12695 -> lopt in
                           (log cfg
                              (fun uu____12701  ->
                                 let uu____12702 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12702);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12715 = cfg in
                               {
                                 steps = (uu___236_12715.steps);
                                 tcenv = (uu___236_12715.tcenv);
                                 delta_level = (uu___236_12715.delta_level);
                                 primitive_steps =
                                   (uu___236_12715.primitive_steps);
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
                      (fun uu____12764  ->
                         fun stack1  ->
                           match uu____12764 with
                           | (a,aq) ->
                               let uu____12776 =
                                 let uu____12777 =
                                   let uu____12784 =
                                     let uu____12785 =
                                       let uu____12816 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12816, false) in
                                     Clos uu____12785 in
                                   (uu____12784, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12777 in
                               uu____12776 :: stack1) args) in
               (log cfg
                  (fun uu____12892  ->
                     let uu____12893 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12893);
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
                             ((let uu___237_12929 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___237_12929.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___237_12929.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12930 ->
                      let uu____12935 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12935)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12938 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12938 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12969 =
                          let uu____12970 =
                            let uu____12977 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___238_12979 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___238_12979.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___238_12979.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12977) in
                          FStar_Syntax_Syntax.Tm_refine uu____12970 in
                        mk uu____12969 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12998 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12998
               else
                 (let uu____13000 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13000 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13008 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13032  -> dummy :: env1) env) in
                        norm_comp cfg uu____13008 c1 in
                      let t2 =
                        let uu____13054 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13054 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13113)::uu____13114 ->
                    (log cfg
                       (fun uu____13125  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13126)::uu____13127 ->
                    (log cfg
                       (fun uu____13138  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13139,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13140;
                                   FStar_Syntax_Syntax.vars = uu____13141;_},uu____13142,uu____13143))::uu____13144
                    ->
                    (log cfg
                       (fun uu____13153  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13154)::uu____13155 ->
                    (log cfg
                       (fun uu____13166  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13167 ->
                    (log cfg
                       (fun uu____13170  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13174  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13191 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13191
                         | FStar_Util.Inr c ->
                             let uu____13199 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13199 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13205 =
                         let uu____13206 =
                           let uu____13207 =
                             let uu____13234 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13234, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13207 in
                         mk uu____13206 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack uu____13205))))
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
                         let uu____13344 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13344 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___239_13364 = cfg in
                               let uu____13365 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___239_13364.steps);
                                 tcenv = uu____13365;
                                 delta_level = (uu___239_13364.delta_level);
                                 primitive_steps =
                                   (uu___239_13364.primitive_steps);
                                 strong = (uu___239_13364.strong)
                               } in
                             let norm1 t2 =
                               let uu____13370 =
                                 let uu____13371 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13371 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13370 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___240_13374 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___240_13374.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___240_13374.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13375 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13375
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13386,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13387;
                               FStar_Syntax_Syntax.lbunivs = uu____13388;
                               FStar_Syntax_Syntax.lbtyp = uu____13389;
                               FStar_Syntax_Syntax.lbeff = uu____13390;
                               FStar_Syntax_Syntax.lbdef = uu____13391;_}::uu____13392),uu____13393)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13429 =
                 (let uu____13432 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13432) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13434 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13434))) in
               if uu____13429
               then
                 let binder =
                   let uu____13436 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13436 in
                 let env1 =
                   let uu____13446 =
                     let uu____13453 =
                       let uu____13454 =
                         let uu____13485 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13485,
                           false) in
                       Clos uu____13454 in
                     ((FStar_Pervasives_Native.Some binder), uu____13453) in
                   uu____13446 :: env in
                 (log cfg
                    (fun uu____13570  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13572 =
                    let uu____13577 =
                      let uu____13578 =
                        let uu____13579 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13579
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13578] in
                    FStar_Syntax_Subst.open_term uu____13577 body in
                  match uu____13572 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13588  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13596 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13596 in
                          FStar_Util.Inl
                            (let uu___241_13606 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___241_13606.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___241_13606.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13609  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___242_13611 = lb in
                           let uu____13612 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___242_13611.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___242_13611.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13612
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13647  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___243_13667 = cfg in
                           {
                             steps = (uu___243_13667.steps);
                             tcenv = (uu___243_13667.tcenv);
                             delta_level = (uu___243_13667.delta_level);
                             primitive_steps =
                               (uu___243_13667.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13670  ->
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
               let uu____13687 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13687 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13723 =
                               let uu___244_13724 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___244_13724.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___244_13724.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13723 in
                           let uu____13725 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13725 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13751 =
                                   FStar_List.map (fun uu____13767  -> dummy)
                                     lbs1 in
                                 let uu____13768 =
                                   let uu____13777 =
                                     FStar_List.map
                                       (fun uu____13797  -> dummy) xs1 in
                                   FStar_List.append uu____13777 env in
                                 FStar_List.append uu____13751 uu____13768 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13821 =
                                       let uu___245_13822 = rc in
                                       let uu____13823 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___245_13822.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13823;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___245_13822.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13821
                                 | uu____13830 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___246_13834 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___246_13834.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___246_13834.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13844 =
                        FStar_List.map (fun uu____13860  -> dummy) lbs2 in
                      FStar_List.append uu____13844 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13868 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13868 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___247_13884 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___247_13884.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___247_13884.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13911 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13911
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13930 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14006  ->
                        match uu____14006 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___248_14127 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___248_14127.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___248_14127.FStar_Syntax_Syntax.sort)
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
               (match uu____13930 with
                | (rec_env,memos,uu____14324) ->
                    let uu____14377 =
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
                             let uu____14908 =
                               let uu____14915 =
                                 let uu____14916 =
                                   let uu____14947 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14947, false) in
                                 Clos uu____14916 in
                               (FStar_Pervasives_Native.None, uu____14915) in
                             uu____14908 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15052 =
                      let uu____15053 = should_reify cfg stack in
                      Prims.op_Negation uu____15053 in
                    if uu____15052
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____15063 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15063
                        then
                          let uu___249_15064 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___249_15064.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___249_15064.primitive_steps);
                            strong = (uu___249_15064.strong)
                          }
                        else
                          (let uu___250_15066 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___250_15066.tcenv);
                             delta_level = (uu___250_15066.delta_level);
                             primitive_steps =
                               (uu___250_15066.primitive_steps);
                             strong = (uu___250_15066.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15068 =
                         let uu____15069 = FStar_Syntax_Subst.compress head1 in
                         uu____15069.FStar_Syntax_Syntax.n in
                       match uu____15068 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15087 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15087 with
                            | (uu____15088,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15094 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15102 =
                                         let uu____15103 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15103.FStar_Syntax_Syntax.n in
                                       match uu____15102 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15109,uu____15110))
                                           ->
                                           let uu____15119 =
                                             let uu____15120 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15120.FStar_Syntax_Syntax.n in
                                           (match uu____15119 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15126,msrc,uu____15128))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15137 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15137
                                            | uu____15138 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15139 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15140 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15140 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___251_15145 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___251_15145.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___251_15145.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___251_15145.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15146 =
                                            FStar_List.tl stack in
                                          let uu____15147 =
                                            let uu____15148 =
                                              let uu____15151 =
                                                let uu____15152 =
                                                  let uu____15165 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15165) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15152 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15151 in
                                            uu____15148
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15146
                                            uu____15147
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15181 =
                                            let uu____15182 = is_return body in
                                            match uu____15182 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15186;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15187;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15192 -> false in
                                          if uu____15181
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
                                               let uu____15216 =
                                                 let uu____15219 =
                                                   let uu____15220 =
                                                     let uu____15237 =
                                                       let uu____15240 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15240] in
                                                     (uu____15237, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15220 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15219 in
                                               uu____15216
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15256 =
                                                 let uu____15257 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15257.FStar_Syntax_Syntax.n in
                                               match uu____15256 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15263::uu____15264::[])
                                                   ->
                                                   let uu____15271 =
                                                     let uu____15274 =
                                                       let uu____15275 =
                                                         let uu____15282 =
                                                           let uu____15285 =
                                                             let uu____15286
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15286 in
                                                           let uu____15287 =
                                                             let uu____15290
                                                               =
                                                               let uu____15291
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15291 in
                                                             [uu____15290] in
                                                           uu____15285 ::
                                                             uu____15287 in
                                                         (bind1, uu____15282) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15275 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15274 in
                                                   uu____15271
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15299 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15305 =
                                                 let uu____15308 =
                                                   let uu____15309 =
                                                     let uu____15324 =
                                                       let uu____15327 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15328 =
                                                         let uu____15331 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15332 =
                                                           let uu____15335 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15336 =
                                                             let uu____15339
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15340
                                                               =
                                                               let uu____15343
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15344
                                                                 =
                                                                 let uu____15347
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15347] in
                                                               uu____15343 ::
                                                                 uu____15344 in
                                                             uu____15339 ::
                                                               uu____15340 in
                                                           uu____15335 ::
                                                             uu____15336 in
                                                         uu____15331 ::
                                                           uu____15332 in
                                                       uu____15327 ::
                                                         uu____15328 in
                                                     (bind_inst, uu____15324) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15309 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15308 in
                                               uu____15305
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15355 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____15355 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15379 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15379 with
                            | (uu____15380,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15415 =
                                        let uu____15416 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15416.FStar_Syntax_Syntax.n in
                                      match uu____15415 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15422) -> t4
                                      | uu____15427 -> head2 in
                                    let uu____15428 =
                                      let uu____15429 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15429.FStar_Syntax_Syntax.n in
                                    match uu____15428 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15435 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15436 = maybe_extract_fv head2 in
                                  match uu____15436 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15446 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15446
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15451 =
                                          maybe_extract_fv head3 in
                                        match uu____15451 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15456 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15457 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15462 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15477 =
                                    match uu____15477 with
                                    | (e,q) ->
                                        let uu____15484 =
                                          let uu____15485 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15485.FStar_Syntax_Syntax.n in
                                        (match uu____15484 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15500 -> false) in
                                  let uu____15501 =
                                    let uu____15502 =
                                      let uu____15509 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15509 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15502 in
                                  if uu____15501
                                  then
                                    let uu____15514 =
                                      let uu____15515 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15515 in
                                    failwith uu____15514
                                  else ());
                                 (let uu____15517 =
                                    maybe_unfold_action head_app in
                                  match uu____15517 with
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
                                      let uu____15556 = FStar_List.tl stack in
                                      norm cfg env uu____15556 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15570 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15570 in
                           let uu____15571 = FStar_List.tl stack in
                           norm cfg env uu____15571 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15692  ->
                                     match uu____15692 with
                                     | (pat,wopt,tm) ->
                                         let uu____15740 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15740))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15772 = FStar_List.tl stack in
                           norm cfg env uu____15772 tm
                       | uu____15773 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15781 = should_reify cfg stack in
                    if uu____15781
                    then
                      let uu____15782 = FStar_List.tl stack in
                      let uu____15783 =
                        let uu____15784 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15784 in
                      norm cfg env uu____15782 uu____15783
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15787 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15787
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___252_15796 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___252_15796.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___252_15796.primitive_steps);
                             strong = (uu___252_15796.strong)
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
                | uu____15798 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____15800::uu____15801 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15806) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15807 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____15838 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15852 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15852
                             | uu____15863 -> m in
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
              let uu____15875 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15875 in
            let uu____15876 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15876 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15889  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15900  ->
                      let uu____15901 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15902 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15901
                        uu____15902);
                 (let t1 =
                    let uu____15904 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15904
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
                    | (UnivArgs (us',uu____15914))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15969 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15972 ->
                        let uu____15975 =
                          let uu____15976 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15976 in
                        failwith uu____15975
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
              let uu____15986 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15986 with
              | (uu____15987,return_repr) ->
                  let return_inst =
                    let uu____15996 =
                      let uu____15997 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15997.FStar_Syntax_Syntax.n in
                    match uu____15996 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16003::[]) ->
                        let uu____16010 =
                          let uu____16013 =
                            let uu____16014 =
                              let uu____16021 =
                                let uu____16024 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16024] in
                              (return_tm, uu____16021) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16014 in
                          FStar_Syntax_Syntax.mk uu____16013 in
                        uu____16010 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16032 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16035 =
                    let uu____16038 =
                      let uu____16039 =
                        let uu____16054 =
                          let uu____16057 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16058 =
                            let uu____16061 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16061] in
                          uu____16057 :: uu____16058 in
                        (return_inst, uu____16054) in
                      FStar_Syntax_Syntax.Tm_app uu____16039 in
                    FStar_Syntax_Syntax.mk uu____16038 in
                  uu____16035 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16070 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16070 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16073 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16073
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16074;
                     FStar_TypeChecker_Env.mtarget = uu____16075;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16076;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16087;
                     FStar_TypeChecker_Env.mtarget = uu____16088;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16089;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16107 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16107)
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
                (fun uu____16163  ->
                   match uu____16163 with
                   | (a,imp) ->
                       let uu____16174 = norm cfg env [] a in
                       (uu____16174, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___253_16191 = comp1 in
            let uu____16194 =
              let uu____16195 =
                let uu____16204 = norm cfg env [] t in
                let uu____16205 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16204, uu____16205) in
              FStar_Syntax_Syntax.Total uu____16195 in
            {
              FStar_Syntax_Syntax.n = uu____16194;
              FStar_Syntax_Syntax.pos =
                (uu___253_16191.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___253_16191.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___254_16220 = comp1 in
            let uu____16223 =
              let uu____16224 =
                let uu____16233 = norm cfg env [] t in
                let uu____16234 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16233, uu____16234) in
              FStar_Syntax_Syntax.GTotal uu____16224 in
            {
              FStar_Syntax_Syntax.n = uu____16223;
              FStar_Syntax_Syntax.pos =
                (uu___254_16220.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___254_16220.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16286  ->
                      match uu____16286 with
                      | (a,i) ->
                          let uu____16297 = norm cfg env [] a in
                          (uu____16297, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___201_16308  ->
                      match uu___201_16308 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16312 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16312
                      | f -> f)) in
            let uu___255_16316 = comp1 in
            let uu____16319 =
              let uu____16320 =
                let uu___256_16321 = ct in
                let uu____16322 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16323 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16326 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16322;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___256_16321.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16323;
                  FStar_Syntax_Syntax.effect_args = uu____16326;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16320 in
            {
              FStar_Syntax_Syntax.n = uu____16319;
              FStar_Syntax_Syntax.pos =
                (uu___255_16316.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___255_16316.FStar_Syntax_Syntax.vars)
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
            (let uu___257_16344 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___257_16344.tcenv);
               delta_level = (uu___257_16344.delta_level);
               primitive_steps = (uu___257_16344.primitive_steps);
               strong = (uu___257_16344.strong)
             }) env [] t in
        let non_info t =
          let uu____16349 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16349 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16352 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___258_16371 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___258_16371.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___258_16371.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16378 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16378
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
                    let uu___259_16389 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___259_16389.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___259_16389.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___259_16389.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___260_16391 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___260_16391.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___260_16391.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___260_16391.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___260_16391.FStar_Syntax_Syntax.flags)
                    } in
              let uu___261_16392 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___261_16392.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___261_16392.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16394 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16397  ->
        match uu____16397 with
        | (x,imp) ->
            let uu____16400 =
              let uu___262_16401 = x in
              let uu____16402 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___262_16401.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___262_16401.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16402
              } in
            (uu____16400, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16408 =
          FStar_List.fold_left
            (fun uu____16426  ->
               fun b  ->
                 match uu____16426 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16408 with | (nbs,uu____16466) -> FStar_List.rev nbs
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
            let uu____16482 =
              let uu___263_16483 = rc in
              let uu____16484 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___263_16483.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16484;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___263_16483.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16482
        | uu____16491 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16504  ->
               let uu____16505 = FStar_Syntax_Print.tag_of_term t in
               let uu____16506 = FStar_Syntax_Print.term_to_string t in
               let uu____16507 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16514 =
                 let uu____16515 =
                   let uu____16518 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16518 in
                 stack_to_string uu____16515 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16505 uu____16506 uu____16507 uu____16514);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16547 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16547
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16549 =
                     let uu____16550 =
                       let uu____16551 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16551 in
                     FStar_Util.string_of_int uu____16550 in
                   let uu____16556 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16557 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16549 uu____16556 uu____16557
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___264_16575 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___264_16575.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___264_16575.strong)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16616  ->
                     let uu____16617 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16617);
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
               let uu____16653 =
                 let uu___265_16654 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___265_16654.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___265_16654.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16653
           | (Arg (Univ uu____16655,uu____16656,uu____16657))::uu____16658 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16661,uu____16662))::uu____16663 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16679),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16732  ->
                     let uu____16733 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16733);
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
                  (let uu____16743 = FStar_ST.op_Bang m in
                   match uu____16743 with
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
                   | FStar_Pervasives_Native.Some (uu____16887,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16930 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16930
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16942  ->
                     let uu____16943 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16943);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16948 =
                   log cfg
                     (fun uu____16953  ->
                        let uu____16954 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16955 =
                          let uu____16956 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16973  ->
                                    match uu____16973 with
                                    | (p,uu____16983,uu____16984) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16956
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16954 uu____16955);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___202_17001  ->
                                match uu___202_17001 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17002 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___266_17006 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___266_17006.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___266_17006.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17038 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17059 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17119  ->
                                    fun uu____17120  ->
                                      match (uu____17119, uu____17120) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17211 = norm_pat env3 p1 in
                                          (match uu____17211 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17059 with
                           | (pats1,env3) ->
                               ((let uu___267_17293 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___267_17293.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___268_17312 = x in
                            let uu____17313 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___268_17312.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___268_17312.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17313
                            } in
                          ((let uu___269_17327 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___269_17327.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___270_17338 = x in
                            let uu____17339 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___270_17338.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___270_17338.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17339
                            } in
                          ((let uu___271_17353 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___271_17353.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___272_17369 = x in
                            let uu____17370 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___272_17369.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___272_17369.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17370
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___273_17377 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___273_17377.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17387 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17401 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17401 with
                                  | (p,wopt,e) ->
                                      let uu____17421 = norm_pat env1 p in
                                      (match uu____17421 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17446 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17446 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17452 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17452) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17462) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17467 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17468;
                         FStar_Syntax_Syntax.fv_delta = uu____17469;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17470;
                         FStar_Syntax_Syntax.fv_delta = uu____17471;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17472);_}
                       -> true
                   | uu____17479 -> false in
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
                   let uu____17624 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17624 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17711 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17750 ->
                                 let uu____17751 =
                                   let uu____17752 = is_cons head1 in
                                   Prims.op_Negation uu____17752 in
                                 FStar_Util.Inr uu____17751)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17777 =
                              let uu____17778 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17778.FStar_Syntax_Syntax.n in
                            (match uu____17777 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17796 ->
                                 let uu____17797 =
                                   let uu____17798 = is_cons head1 in
                                   Prims.op_Negation uu____17798 in
                                 FStar_Util.Inr uu____17797))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17867)::rest_a,(p1,uu____17870)::rest_p) ->
                       let uu____17914 = matches_pat t1 p1 in
                       (match uu____17914 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17963 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18069 = matches_pat scrutinee1 p1 in
                       (match uu____18069 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18109  ->
                                  let uu____18110 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18111 =
                                    let uu____18112 =
                                      FStar_List.map
                                        (fun uu____18122  ->
                                           match uu____18122 with
                                           | (uu____18127,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18112
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18110 uu____18111);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18158  ->
                                       match uu____18158 with
                                       | (bv,t1) ->
                                           let uu____18181 =
                                             let uu____18188 =
                                               let uu____18191 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18191 in
                                             let uu____18192 =
                                               let uu____18193 =
                                                 let uu____18224 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18224, false) in
                                               Clos uu____18193 in
                                             (uu____18188, uu____18192) in
                                           uu____18181 :: env2) env1 s in
                              let uu____18333 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18333))) in
                 let uu____18334 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18334
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___203_18355  ->
                match uu___203_18355 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18359 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18365 -> d in
      let uu____18368 = built_in_primitive_steps e in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = uu____18368;
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
            let uu___274_18393 = config s e in
            {
              steps = (uu___274_18393.steps);
              tcenv = (uu___274_18393.tcenv);
              delta_level = (uu___274_18393.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___274_18393.strong)
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
      fun t  -> let uu____18418 = config s e in norm_comp uu____18418 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18431 = config [] env in norm_universe uu____18431 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18444 = config [] env in ghost_to_pure_aux uu____18444 [] c
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
        let uu____18462 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18462 in
      let uu____18469 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18469
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___275_18471 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___275_18471.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___275_18471.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18474  ->
                    let uu____18475 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18475))
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
            ((let uu____18492 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18492);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18503 = config [AllowUnboundUniverses] env in
          norm_comp uu____18503 [] c
        with
        | e ->
            ((let uu____18516 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18516);
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
                   let uu____18553 =
                     let uu____18554 =
                       let uu____18561 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18561) in
                     FStar_Syntax_Syntax.Tm_refine uu____18554 in
                   mk uu____18553 t01.FStar_Syntax_Syntax.pos
               | uu____18566 -> t2)
          | uu____18567 -> t2 in
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
        let uu____18607 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18607 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18636 ->
                 let uu____18643 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18643 with
                  | (actuals,uu____18653,uu____18654) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18668 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18668 with
                         | (binders,args) ->
                             let uu____18685 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18685
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
      | uu____18693 ->
          let uu____18694 = FStar_Syntax_Util.head_and_args t in
          (match uu____18694 with
           | (head1,args) ->
               let uu____18731 =
                 let uu____18732 = FStar_Syntax_Subst.compress head1 in
                 uu____18732.FStar_Syntax_Syntax.n in
               (match uu____18731 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18735,thead) ->
                    let uu____18761 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18761 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18803 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___280_18811 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___280_18811.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___280_18811.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___280_18811.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___280_18811.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___280_18811.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___280_18811.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___280_18811.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___280_18811.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___280_18811.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___280_18811.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___280_18811.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___280_18811.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___280_18811.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___280_18811.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___280_18811.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___280_18811.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___280_18811.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___280_18811.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___280_18811.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___280_18811.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___280_18811.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___280_18811.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___280_18811.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___280_18811.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___280_18811.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___280_18811.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___280_18811.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___280_18811.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___280_18811.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___280_18811.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___280_18811.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18803 with
                            | (uu____18812,ty,uu____18814) ->
                                eta_expand_with_type env t ty))
                | uu____18815 ->
                    let uu____18816 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___281_18824 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___281_18824.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___281_18824.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___281_18824.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___281_18824.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___281_18824.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___281_18824.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___281_18824.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___281_18824.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___281_18824.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___281_18824.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___281_18824.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___281_18824.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___281_18824.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___281_18824.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___281_18824.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___281_18824.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___281_18824.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___281_18824.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___281_18824.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___281_18824.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___281_18824.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___281_18824.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___281_18824.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___281_18824.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___281_18824.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___281_18824.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___281_18824.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___281_18824.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___281_18824.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___281_18824.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___281_18824.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18816 with
                     | (uu____18825,ty,uu____18827) ->
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
            | (uu____18901,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18907,FStar_Util.Inl t) ->
                let uu____18913 =
                  let uu____18916 =
                    let uu____18917 =
                      let uu____18930 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18930) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18917 in
                  FStar_Syntax_Syntax.mk uu____18916 in
                uu____18913 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18934 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18934 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18961 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19016 ->
                    let uu____19017 =
                      let uu____19026 =
                        let uu____19027 = FStar_Syntax_Subst.compress t3 in
                        uu____19027.FStar_Syntax_Syntax.n in
                      (uu____19026, tc) in
                    (match uu____19017 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19052) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19089) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19128,FStar_Util.Inl uu____19129) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19152 -> failwith "Impossible") in
              (match uu____18961 with
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
          let uu____19257 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19257 with
          | (univ_names1,binders1,tc) ->
              let uu____19315 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19315)
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
          let uu____19350 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19350 with
          | (univ_names1,binders1,tc) ->
              let uu____19410 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19410)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19443 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19443 with
           | (univ_names1,binders1,typ1) ->
               let uu___282_19471 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___282_19471.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___282_19471.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___282_19471.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___282_19471.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___283_19492 = s in
          let uu____19493 =
            let uu____19494 =
              let uu____19503 = FStar_List.map (elim_uvars env) sigs in
              (uu____19503, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19494 in
          {
            FStar_Syntax_Syntax.sigel = uu____19493;
            FStar_Syntax_Syntax.sigrng =
              (uu___283_19492.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___283_19492.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___283_19492.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___283_19492.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19520 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19520 with
           | (univ_names1,uu____19538,typ1) ->
               let uu___284_19552 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___284_19552.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___284_19552.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___284_19552.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___284_19552.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19558 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19558 with
           | (univ_names1,uu____19576,typ1) ->
               let uu___285_19590 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___285_19590.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___285_19590.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___285_19590.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___285_19590.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19624 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19624 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19647 =
                            let uu____19648 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19648 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19647 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___286_19651 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___286_19651.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___286_19651.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___287_19652 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___287_19652.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___287_19652.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___287_19652.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___287_19652.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___288_19664 = s in
          let uu____19665 =
            let uu____19666 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19666 in
          {
            FStar_Syntax_Syntax.sigel = uu____19665;
            FStar_Syntax_Syntax.sigrng =
              (uu___288_19664.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___288_19664.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___288_19664.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___288_19664.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19670 = elim_uvars_aux_t env us [] t in
          (match uu____19670 with
           | (us1,uu____19688,t1) ->
               let uu___289_19702 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___289_19702.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___289_19702.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___289_19702.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___289_19702.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19703 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19705 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19705 with
           | (univs1,binders,signature) ->
               let uu____19733 =
                 let uu____19742 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19742 with
                 | (univs_opening,univs2) ->
                     let uu____19769 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19769) in
               (match uu____19733 with
                | (univs_opening,univs_closing) ->
                    let uu____19786 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19792 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19793 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19792, uu____19793) in
                    (match uu____19786 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19815 =
                           match uu____19815 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19833 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19833 with
                                | (us1,t1) ->
                                    let uu____19844 =
                                      let uu____19849 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19856 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19849, uu____19856) in
                                    (match uu____19844 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19869 =
                                           let uu____19874 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19883 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19874, uu____19883) in
                                         (match uu____19869 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19899 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19899 in
                                              let uu____19900 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19900 with
                                               | (uu____19921,uu____19922,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19937 =
                                                       let uu____19938 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19938 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19937 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19943 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19943 with
                           | (uu____19956,uu____19957,t1) -> t1 in
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
                             | uu____20017 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20034 =
                               let uu____20035 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20035.FStar_Syntax_Syntax.n in
                             match uu____20034 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20094 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20123 =
                               let uu____20124 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20124.FStar_Syntax_Syntax.n in
                             match uu____20123 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20145) ->
                                 let uu____20166 = destruct_action_body body in
                                 (match uu____20166 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20211 ->
                                 let uu____20212 = destruct_action_body t in
                                 (match uu____20212 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20261 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20261 with
                           | (action_univs,t) ->
                               let uu____20270 = destruct_action_typ_templ t in
                               (match uu____20270 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___290_20311 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___290_20311.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___290_20311.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___291_20313 = ed in
                           let uu____20314 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20315 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20316 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20317 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20318 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20319 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20320 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20321 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20322 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20323 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20324 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20325 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20326 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20327 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___291_20313.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___291_20313.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20314;
                             FStar_Syntax_Syntax.bind_wp = uu____20315;
                             FStar_Syntax_Syntax.if_then_else = uu____20316;
                             FStar_Syntax_Syntax.ite_wp = uu____20317;
                             FStar_Syntax_Syntax.stronger = uu____20318;
                             FStar_Syntax_Syntax.close_wp = uu____20319;
                             FStar_Syntax_Syntax.assert_p = uu____20320;
                             FStar_Syntax_Syntax.assume_p = uu____20321;
                             FStar_Syntax_Syntax.null_wp = uu____20322;
                             FStar_Syntax_Syntax.trivial = uu____20323;
                             FStar_Syntax_Syntax.repr = uu____20324;
                             FStar_Syntax_Syntax.return_repr = uu____20325;
                             FStar_Syntax_Syntax.bind_repr = uu____20326;
                             FStar_Syntax_Syntax.actions = uu____20327
                           } in
                         let uu___292_20330 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___292_20330.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___292_20330.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___292_20330.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___292_20330.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___204_20347 =
            match uu___204_20347 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20374 = elim_uvars_aux_t env us [] t in
                (match uu____20374 with
                 | (us1,uu____20398,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___293_20417 = sub_eff in
            let uu____20418 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20421 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___293_20417.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___293_20417.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20418;
              FStar_Syntax_Syntax.lift = uu____20421
            } in
          let uu___294_20424 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___294_20424.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___294_20424.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___294_20424.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___294_20424.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20434 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20434 with
           | (univ_names1,binders1,comp1) ->
               let uu___295_20468 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___295_20468.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___295_20468.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___295_20468.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___295_20468.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20479 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t