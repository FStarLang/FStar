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
  fun projectee  -> match projectee with | Beta  -> true | uu____19 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____24 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____29 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____48 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____53 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____58 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____63 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____68 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____73 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____79 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____95 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____119 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____124 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____129 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____134 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____139 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____144 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____149 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____154 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____159 -> false
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____196  -> []) }
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
    match projectee with | Clos _0 -> true | uu____403 -> false
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
    match projectee with | Univ _0 -> true | uu____507 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____520 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___178_540  ->
    match uu___178_540 with
    | Clos (uu____541,t,uu____543,uu____544) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____589 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} ->
        __fname__primitive_steps
let only_strong_steps':
  primitive_step Prims.list -> primitive_step Prims.list =
  fun steps  -> FStar_List.filter (fun ps  -> ps.strong_reduction_ok) steps
let only_strong_steps: cfg -> cfg =
  fun cfg  ->
    let uu___195_682 = cfg in
    let uu____683 = only_strong_steps' cfg.primitive_steps in
    {
      steps = (uu___195_682.steps);
      tcenv = (uu___195_682.tcenv);
      delta_level = (uu___195_682.delta_level);
      primitive_steps = uu____683
    }
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
    match projectee with | Arg _0 -> true | uu____830 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____868 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____906 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____965 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1009 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1067 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1109 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1143 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1191 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1239 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1268 .
    'Auu____1268 ->
      FStar_Range.range -> 'Auu____1268 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1319 = FStar_ST.op_Bang r in
      match uu____1319 with
      | FStar_Pervasives_Native.Some uu____1386 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1459 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1459 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___179_1467  ->
    match uu___179_1467 with
    | Arg (c,uu____1469,uu____1470) ->
        let uu____1471 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1471
    | MemoLazy uu____1472 -> "MemoLazy"
    | Abs (uu____1479,bs,uu____1481,uu____1482,uu____1483) ->
        let uu____1488 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1488
    | UnivArgs uu____1493 -> "UnivArgs"
    | Match uu____1500 -> "Match"
    | App (uu____1507,t,uu____1509,uu____1510) ->
        let uu____1511 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1511
    | Meta (m,uu____1513) -> "Meta"
    | Let uu____1514 -> "Let"
    | Steps (uu____1523,uu____1524,uu____1525) -> "Steps"
    | Debug (t,uu____1535) ->
        let uu____1536 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1536
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1545 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1545 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1563 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1563 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1578 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1578 then f () else ()
let is_empty: 'Auu____1584 . 'Auu____1584 Prims.list -> Prims.bool =
  fun uu___180_1590  ->
    match uu___180_1590 with | [] -> true | uu____1593 -> false
let lookup_bvar:
  'Auu____1604 'Auu____1605 .
    ('Auu____1605,'Auu____1604) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1604
  =
  fun env  ->
    fun x  ->
      try
        let uu____1629 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1629
      with
      | uu____1642 ->
          let uu____1643 =
            let uu____1644 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1644 in
          failwith uu____1643
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
          let uu____1685 =
            FStar_List.fold_left
              (fun uu____1711  ->
                 fun u1  ->
                   match uu____1711 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1736 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1736 with
                        | (k_u,n1) ->
                            let uu____1751 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1751
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1685 with
          | (uu____1769,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1794 =
                   let uu____1795 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1795 in
                 match uu____1794 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1813 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1822 ->
                   let uu____1823 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1823
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1829 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1838 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1847 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1854 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1854 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1871 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1871 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1879 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1887 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1887 with
                                  | (uu____1892,m) -> n1 <= m)) in
                        if uu____1879 then rest1 else us1
                    | uu____1897 -> us1)
               | uu____1902 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1906 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____1906 in
        let uu____1909 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1909
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1911 = aux u in
           match uu____1911 with
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
          (fun uu____2015  ->
             let uu____2016 = FStar_Syntax_Print.tag_of_term t in
             let uu____2017 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2016
               uu____2017);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2024 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2026 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2051 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2052 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2053 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2054 ->
                  let uu____2071 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2071
                  then
                    let uu____2072 =
                      let uu____2073 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2074 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2073 uu____2074 in
                    failwith uu____2072
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2077 =
                    let uu____2078 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2078 in
                  mk uu____2077 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2085 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2085
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2087 = lookup_bvar env x in
                  (match uu____2087 with
                   | Univ uu____2090 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2094) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2206 = closures_as_binders_delayed cfg env bs in
                  (match uu____2206 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2234 =
                         let uu____2235 =
                           let uu____2252 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2252) in
                         FStar_Syntax_Syntax.Tm_abs uu____2235 in
                       mk uu____2234 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2283 = closures_as_binders_delayed cfg env bs in
                  (match uu____2283 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2325 =
                    let uu____2336 =
                      let uu____2343 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2343] in
                    closures_as_binders_delayed cfg env uu____2336 in
                  (match uu____2325 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2361 =
                         let uu____2362 =
                           let uu____2369 =
                             let uu____2370 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2370
                               FStar_Pervasives_Native.fst in
                           (uu____2369, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2362 in
                       mk uu____2361 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2461 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2461
                    | FStar_Util.Inr c ->
                        let uu____2475 = close_comp cfg env c in
                        FStar_Util.Inr uu____2475 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2491 =
                    let uu____2492 =
                      let uu____2519 = closure_as_term_delayed cfg env t11 in
                      (uu____2519, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2492 in
                  mk uu____2491 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2570 =
                    let uu____2571 =
                      let uu____2578 = closure_as_term_delayed cfg env t' in
                      let uu____2581 =
                        let uu____2582 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2582 in
                      (uu____2578, uu____2581) in
                    FStar_Syntax_Syntax.Tm_meta uu____2571 in
                  mk uu____2570 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2642 =
                    let uu____2643 =
                      let uu____2650 = closure_as_term_delayed cfg env t' in
                      let uu____2653 =
                        let uu____2654 =
                          let uu____2661 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2661) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2654 in
                      (uu____2650, uu____2653) in
                    FStar_Syntax_Syntax.Tm_meta uu____2643 in
                  mk uu____2642 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2680 =
                    let uu____2681 =
                      let uu____2688 = closure_as_term_delayed cfg env t' in
                      let uu____2691 =
                        let uu____2692 =
                          let uu____2701 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2701) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2692 in
                      (uu____2688, uu____2691) in
                    FStar_Syntax_Syntax.Tm_meta uu____2681 in
                  mk uu____2680 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2714 =
                    let uu____2715 =
                      let uu____2722 = closure_as_term_delayed cfg env t' in
                      (uu____2722, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2715 in
                  mk uu____2714 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2762  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2781 =
                    let uu____2792 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2792
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2811 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___200_2823 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___200_2823.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___200_2823.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2811)) in
                  (match uu____2781 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___201_2839 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___201_2839.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___201_2839.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2850,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2909  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2934 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2934
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2954  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2976 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2976
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___202_2988 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___202_2988.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___202_2988.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___203_2989 = lb in
                    let uu____2990 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___203_2989.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___203_2989.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2990
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3020  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3109 =
                    match uu____3109 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3164 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3185 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3245  ->
                                        fun uu____3246  ->
                                          match (uu____3245, uu____3246) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3337 =
                                                norm_pat env3 p1 in
                                              (match uu____3337 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3185 with
                               | (pats1,env3) ->
                                   ((let uu___204_3419 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___204_3419.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___205_3438 = x in
                                let uu____3439 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___205_3438.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___205_3438.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3439
                                } in
                              ((let uu___206_3453 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___206_3453.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___207_3464 = x in
                                let uu____3465 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___207_3464.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___207_3464.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3465
                                } in
                              ((let uu___208_3479 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___208_3479.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___209_3495 = x in
                                let uu____3496 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___209_3495.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___209_3495.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3496
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___210_3503 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___210_3503.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3506 = norm_pat env1 pat in
                        (match uu____3506 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3535 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3535 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3541 =
                    let uu____3542 =
                      let uu____3565 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3565) in
                    FStar_Syntax_Syntax.Tm_match uu____3542 in
                  mk uu____3541 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3651 -> closure_as_term cfg env t
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
        | uu____3677 ->
            FStar_List.map
              (fun uu____3694  ->
                 match uu____3694 with
                 | (x,imp) ->
                     let uu____3713 = closure_as_term_delayed cfg env x in
                     (uu____3713, imp)) args
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
        let uu____3727 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3776  ->
                  fun uu____3777  ->
                    match (uu____3776, uu____3777) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___211_3847 = b in
                          let uu____3848 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___211_3847.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___211_3847.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3848
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3727 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3941 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3954 = closure_as_term_delayed cfg env t in
                 let uu____3955 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3954 uu____3955
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3968 = closure_as_term_delayed cfg env t in
                 let uu____3969 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3968 uu____3969
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
                        (fun uu___181_3995  ->
                           match uu___181_3995 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3999 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3999
                           | f -> f)) in
                 let uu____4003 =
                   let uu___212_4004 = c1 in
                   let uu____4005 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4005;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___212_4004.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4003)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___182_4015  ->
            match uu___182_4015 with
            | FStar_Syntax_Syntax.DECREASES uu____4016 -> false
            | uu____4019 -> true))
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
                   (fun uu___183_4037  ->
                      match uu___183_4037 with
                      | FStar_Syntax_Syntax.DECREASES uu____4038 -> false
                      | uu____4041 -> true)) in
            let rc1 =
              let uu___213_4043 = rc in
              let uu____4044 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___213_4043.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4044;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4051 -> lopt
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
    let uu____4139 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4139 in
  let arg_as_bounded_int uu____4167 =
    match uu____4167 with
    | (a,uu____4179) ->
        let uu____4186 =
          let uu____4187 = FStar_Syntax_Subst.compress a in
          uu____4187.FStar_Syntax_Syntax.n in
        (match uu____4186 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4197;
                FStar_Syntax_Syntax.vars = uu____4198;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4200;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4201;_},uu____4202)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4241 =
               let uu____4246 = FStar_Util.int_of_string i in
               (fv1, uu____4246) in
             FStar_Pervasives_Native.Some uu____4241
         | uu____4251 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4293 = f a in FStar_Pervasives_Native.Some uu____4293
    | uu____4294 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4344 = f a0 a1 in FStar_Pervasives_Native.Some uu____4344
    | uu____4345 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4394 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4394 in
  let binary_op as_a f res args =
    let uu____4450 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4450 in
  let as_primitive_step uu____4474 =
    match uu____4474 with
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
           let uu____4522 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4522) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4550 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4550) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4571 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4571) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4599 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4599) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4627 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4627) in
  let list_of_string' rng s =
    let name l =
      let uu____4641 =
        let uu____4642 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4642 in
      mk uu____4641 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4652 =
      let uu____4655 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4655 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4652 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    FStar_Syntax_Embeddings.embed_int rng r in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4702 = arg_as_string a1 in
        (match uu____4702 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4708 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4708 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4721 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4721
              | uu____4722 -> FStar_Pervasives_Native.None)
         | uu____4727 -> FStar_Pervasives_Native.None)
    | uu____4730 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4740 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4740 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____4756 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4756 in
  let string_of_bool2 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____4786 args =
    match args with
    | uu____4798::(t,uu____4800)::[] ->
        let uu____4829 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____4829
    | uu____4834 -> FStar_Pervasives_Native.None in
  let set_range_of1 uu____4856 args =
    match args with
    | uu____4866::(t,uu____4868)::(r,uu____4870)::[] ->
        let uu____4891 = FStar_Syntax_Embeddings.unembed_range_safe r in
        FStar_Util.bind_opt uu____4891
          (fun r1  ->
             FStar_Pervasives_Native.Some
               (let uu___214_4901 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_4901.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_4901.FStar_Syntax_Syntax.vars)
                }))
    | uu____4902 -> FStar_Pervasives_Native.None in
  let mk_range1 uu____4918 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4929 =
          let uu____4950 = arg_as_string fn in
          let uu____4953 = arg_as_int from_line in
          let uu____4956 = arg_as_int from_col in
          let uu____4959 = arg_as_int to_line in
          let uu____4962 = arg_as_int to_col in
          (uu____4950, uu____4953, uu____4956, uu____4959, uu____4962) in
        (match uu____4929 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4993 = FStar_Range.mk_pos from_l from_c in
               let uu____4994 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____4993 uu____4994 in
             let uu____4995 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4995
         | uu____5000 -> FStar_Pervasives_Native.None)
    | uu____5021 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5048)::(a1,uu____5050)::(a2,uu____5052)::[] ->
        let uu____5089 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5089 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5102 -> FStar_Pervasives_Native.None)
    | uu____5103 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5121 =
      let uu____5136 =
        let uu____5151 =
          let uu____5166 =
            let uu____5181 =
              let uu____5196 =
                let uu____5211 =
                  let uu____5226 =
                    let uu____5241 =
                      let uu____5256 =
                        let uu____5271 =
                          let uu____5286 =
                            let uu____5301 =
                              let uu____5316 =
                                let uu____5331 =
                                  let uu____5346 =
                                    let uu____5361 =
                                      let uu____5376 =
                                        let uu____5391 =
                                          let uu____5406 =
                                            let uu____5421 =
                                              let uu____5434 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5434,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5441 =
                                              let uu____5456 =
                                                let uu____5469 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5469,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5478 =
                                                let uu____5493 =
                                                  let uu____5508 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5508,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5517 =
                                                  let uu____5534 =
                                                    let uu____5555 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____5555,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____5570 =
                                                    let uu____5593 =
                                                      let uu____5612 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____5612,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____5625 =
                                                      let uu____5646 =
                                                        let uu____5661 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____5661,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____5646] in
                                                    uu____5593 :: uu____5625 in
                                                  uu____5534 :: uu____5570 in
                                                uu____5493 :: uu____5517 in
                                              uu____5456 :: uu____5478 in
                                            uu____5421 :: uu____5441 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5406 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5391 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5376 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5361 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5346 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5331 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5316 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5301 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5286 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5271 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5256 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                FStar_Syntax_Embeddings.embed_bool r (x >= y))))
                      :: uu____5241 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              FStar_Syntax_Embeddings.embed_bool r (x > y))))
                    :: uu____5226 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            FStar_Syntax_Embeddings.embed_bool r (x <= y))))
                  :: uu____5211 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          FStar_Syntax_Embeddings.embed_bool r (x < y))))
                :: uu____5196 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5181 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5166 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5151 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5136 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5121 in
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
      let uu____6250 =
        let uu____6251 =
          let uu____6252 = FStar_Syntax_Syntax.as_arg c in [uu____6252] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6251 in
      uu____6250 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6287 =
              let uu____6300 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6300, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6319  ->
                        fun uu____6320  ->
                          match (uu____6319, uu____6320) with
                          | ((int_to_t1,x),(uu____6339,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6349 =
              let uu____6364 =
                let uu____6377 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6377, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6396  ->
                          fun uu____6397  ->
                            match (uu____6396, uu____6397) with
                            | ((int_to_t1,x),(uu____6416,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6426 =
                let uu____6441 =
                  let uu____6454 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6454, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6473  ->
                            fun uu____6474  ->
                              match (uu____6473, uu____6474) with
                              | ((int_to_t1,x),(uu____6493,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6441] in
              uu____6364 :: uu____6426 in
            uu____6287 :: uu____6349)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6592)::(a1,uu____6594)::(a2,uu____6596)::[] ->
        let uu____6633 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6633 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___215_6639 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___215_6639.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___215_6639.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___216_6643 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_6643.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_6643.FStar_Syntax_Syntax.vars)
                })
         | uu____6644 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6646)::uu____6647::(a1,uu____6649)::(a2,uu____6651)::[] ->
        let uu____6700 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6700 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___215_6706 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___215_6706.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___215_6706.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___216_6710 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_6710.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_6710.FStar_Syntax_Syntax.vars)
                })
         | uu____6711 -> FStar_Pervasives_Native.None)
    | uu____6712 -> failwith "Unexpected number of arguments" in
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
      let uu____6732 =
        let uu____6733 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6733 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6732
    with | uu____6739 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6746 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6746) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6806  ->
           fun subst1  ->
             match uu____6806 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6848)) ->
                      let uu____6907 = b in
                      (match uu____6907 with
                       | (bv,uu____6915) ->
                           let uu____6916 =
                             let uu____6917 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6917 in
                           if uu____6916
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6922 = unembed_binder term1 in
                              match uu____6922 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6929 =
                                      let uu___219_6930 = bv in
                                      let uu____6931 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___219_6930.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___219_6930.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6931
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6929 in
                                  let b_for_x =
                                    let uu____6935 =
                                      let uu____6942 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6942) in
                                    FStar_Syntax_Syntax.NT uu____6935 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___184_6951  ->
                                         match uu___184_6951 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6952,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6954;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6955;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6960 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6961 -> subst1)) env []
let reduce_primops:
  'Auu____6984 'Auu____6985 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6985) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6984 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____7026 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7026
          then tm
          else
            (let uu____7028 = FStar_Syntax_Util.head_and_args tm in
             match uu____7028 with
             | (head1,args) ->
                 let uu____7065 =
                   let uu____7066 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7066.FStar_Syntax_Syntax.n in
                 (match uu____7065 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7070 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7070 with
                       | FStar_Pervasives_Native.None  -> tm
                       | FStar_Pervasives_Native.Some prim_step ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7087  ->
                                   let uu____7088 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7089 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7096 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7088 uu____7089 uu____7096);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7101  ->
                                   let uu____7102 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7102);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7105  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7107 =
                                 prim_step.interpretation psc args in
                               match uu____7107 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7113  ->
                                         let uu____7114 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7114);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7120  ->
                                         let uu____7121 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7122 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7121 uu____7122);
                                    reduced))))
                  | uu____7123 -> tm))
let reduce_equality:
  'Auu____7134 'Auu____7135 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7135) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7134 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___220_7173 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___220_7173.tcenv);
           delta_level = (uu___220_7173.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  'Auu____7186 'Auu____7187 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7187) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7186 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7229 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7229
          then tm1
          else
            (let w t =
               let uu___221_7241 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___221_7241.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___221_7241.FStar_Syntax_Syntax.vars)
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
               | uu____7258 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7298;
                         FStar_Syntax_Syntax.vars = uu____7299;_},uu____7300);
                    FStar_Syntax_Syntax.pos = uu____7301;
                    FStar_Syntax_Syntax.vars = uu____7302;_},args)
                 ->
                 let uu____7328 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7328
                 then
                   let uu____7329 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7329 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7384)::
                        (uu____7385,(arg,uu____7387))::[] -> arg
                    | (uu____7452,(arg,uu____7454))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7455)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7520)::uu____7521::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7584::(FStar_Pervasives_Native.Some (false
                                   ),uu____7585)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7648 -> tm1)
                 else
                   (let uu____7664 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7664
                    then
                      let uu____7665 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7665 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7720)::uu____7721::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7784::(FStar_Pervasives_Native.Some (true
                                     ),uu____7785)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7848)::
                          (uu____7849,(arg,uu____7851))::[] -> arg
                      | (uu____7916,(arg,uu____7918))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7919)::[]
                          -> arg
                      | uu____7984 -> tm1
                    else
                      (let uu____8000 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8000
                       then
                         let uu____8001 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8001 with
                         | uu____8056::(FStar_Pervasives_Native.Some (true
                                        ),uu____8057)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8120)::uu____8121::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8184)::
                             (uu____8185,(arg,uu____8187))::[] -> arg
                         | (uu____8252,(p,uu____8254))::(uu____8255,(q,uu____8257))::[]
                             ->
                             let uu____8322 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8322
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8324 -> tm1
                       else
                         (let uu____8340 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8340
                          then
                            let uu____8341 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8341 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8396)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8435)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8474 -> tm1
                          else
                            (let uu____8490 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8490
                             then
                               match args with
                               | (t,uu____8492)::[] ->
                                   let uu____8509 =
                                     let uu____8510 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8510.FStar_Syntax_Syntax.n in
                                   (match uu____8509 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8513::[],body,uu____8515) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8542 -> tm1)
                                    | uu____8545 -> tm1)
                               | (uu____8546,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8547))::
                                   (t,uu____8549)::[] ->
                                   let uu____8588 =
                                     let uu____8589 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8589.FStar_Syntax_Syntax.n in
                                   (match uu____8588 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8592::[],body,uu____8594) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8621 -> tm1)
                                    | uu____8624 -> tm1)
                               | uu____8625 -> tm1
                             else
                               (let uu____8635 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8635
                                then
                                  match args with
                                  | (t,uu____8637)::[] ->
                                      let uu____8654 =
                                        let uu____8655 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8655.FStar_Syntax_Syntax.n in
                                      (match uu____8654 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8658::[],body,uu____8660)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8687 -> tm1)
                                       | uu____8690 -> tm1)
                                  | (uu____8691,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8692))::(t,uu____8694)::[] ->
                                      let uu____8733 =
                                        let uu____8734 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8734.FStar_Syntax_Syntax.n in
                                      (match uu____8733 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8737::[],body,uu____8739)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8766 -> tm1)
                                       | uu____8769 -> tm1)
                                  | uu____8770 -> tm1
                                else
                                  (let uu____8780 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8780
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8781;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8782;_},uu____8783)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8800;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8801;_},uu____8802)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8819 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8830;
                    FStar_Syntax_Syntax.vars = uu____8831;_},args)
                 ->
                 let uu____8853 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8853
                 then
                   let uu____8854 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8854 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8909)::
                        (uu____8910,(arg,uu____8912))::[] -> arg
                    | (uu____8977,(arg,uu____8979))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8980)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9045)::uu____9046::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9109::(FStar_Pervasives_Native.Some (false
                                   ),uu____9110)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9173 -> tm1)
                 else
                   (let uu____9189 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9189
                    then
                      let uu____9190 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9190 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9245)::uu____9246::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9309::(FStar_Pervasives_Native.Some (true
                                     ),uu____9310)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9373)::
                          (uu____9374,(arg,uu____9376))::[] -> arg
                      | (uu____9441,(arg,uu____9443))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9444)::[]
                          -> arg
                      | uu____9509 -> tm1
                    else
                      (let uu____9525 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9525
                       then
                         let uu____9526 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9526 with
                         | uu____9581::(FStar_Pervasives_Native.Some (true
                                        ),uu____9582)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9645)::uu____9646::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9709)::
                             (uu____9710,(arg,uu____9712))::[] -> arg
                         | (uu____9777,(p,uu____9779))::(uu____9780,(q,uu____9782))::[]
                             ->
                             let uu____9847 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9847
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9849 -> tm1
                       else
                         (let uu____9865 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9865
                          then
                            let uu____9866 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9866 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9921)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9960)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9999 -> tm1
                          else
                            (let uu____10015 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10015
                             then
                               match args with
                               | (t,uu____10017)::[] ->
                                   let uu____10034 =
                                     let uu____10035 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10035.FStar_Syntax_Syntax.n in
                                   (match uu____10034 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10038::[],body,uu____10040) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10067 -> tm1)
                                    | uu____10070 -> tm1)
                               | (uu____10071,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10072))::
                                   (t,uu____10074)::[] ->
                                   let uu____10113 =
                                     let uu____10114 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10114.FStar_Syntax_Syntax.n in
                                   (match uu____10113 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10117::[],body,uu____10119) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10146 -> tm1)
                                    | uu____10149 -> tm1)
                               | uu____10150 -> tm1
                             else
                               (let uu____10160 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10160
                                then
                                  match args with
                                  | (t,uu____10162)::[] ->
                                      let uu____10179 =
                                        let uu____10180 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10180.FStar_Syntax_Syntax.n in
                                      (match uu____10179 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10183::[],body,uu____10185)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10212 -> tm1)
                                       | uu____10215 -> tm1)
                                  | (uu____10216,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10217))::(t,uu____10219)::[] ->
                                      let uu____10258 =
                                        let uu____10259 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10259.FStar_Syntax_Syntax.n in
                                      (match uu____10258 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10262::[],body,uu____10264)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10291 -> tm1)
                                       | uu____10294 -> tm1)
                                  | uu____10295 -> tm1
                                else
                                  (let uu____10305 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10305
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10306;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10307;_},uu____10308)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10325;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10326;_},uu____10327)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10344 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | uu____10354 -> tm1)
let is_norm_request:
  'Auu____10361 .
    FStar_Syntax_Syntax.term -> 'Auu____10361 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10374 =
        let uu____10381 =
          let uu____10382 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10382.FStar_Syntax_Syntax.n in
        (uu____10381, args) in
      match uu____10374 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10388::uu____10389::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10393::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10398::uu____10399::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10402 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___185_10414  ->
    match uu___185_10414 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10420 =
          let uu____10423 =
            let uu____10424 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10424 in
          [uu____10423] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10420
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10443 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10443) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10481 =
          let uu____10484 =
            let uu____10489 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10489 s in
          FStar_All.pipe_right uu____10484 FStar_Util.must in
        FStar_All.pipe_right uu____10481 tr_norm_steps in
      match args with
      | uu____10514::(tm,uu____10516)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10539)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10554)::uu____10555::(tm,uu____10557)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10597 =
              let uu____10600 = full_norm steps in parse_steps uu____10600 in
            Beta :: uu____10597 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10609 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___186_10627  ->
    match uu___186_10627 with
    | (App
        (uu____10630,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10631;
                       FStar_Syntax_Syntax.vars = uu____10632;_},uu____10633,uu____10634))::uu____10635
        -> true
    | uu____10642 -> false
let firstn:
  'Auu____10651 .
    Prims.int ->
      'Auu____10651 Prims.list ->
        ('Auu____10651 Prims.list,'Auu____10651 Prims.list)
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
          (uu____10689,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10690;
                         FStar_Syntax_Syntax.vars = uu____10691;_},uu____10692,uu____10693))::uu____10694
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10701 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10817  ->
               let uu____10818 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10819 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10820 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10827 =
                 let uu____10828 =
                   let uu____10831 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10831 in
                 stack_to_string uu____10828 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10818 uu____10819 uu____10820 uu____10827);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10854 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10879 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10896 =
                 let uu____10897 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10898 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10897 uu____10898 in
               failwith uu____10896
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10899 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10916 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10917 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10918;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10919;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10922;
                 FStar_Syntax_Syntax.fv_delta = uu____10923;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10924;
                 FStar_Syntax_Syntax.fv_delta = uu____10925;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10926);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10934 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10934 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10940  ->
                     let uu____10941 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10942 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10941 uu____10942);
                if b
                then
                  (let uu____10943 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10943 t1 fv)
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
                 let uu___222_10982 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___222_10982.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___222_10982.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11015 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11015) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___223_11023 = cfg in
                 let uu____11024 =
                   FStar_List.filter
                     (fun uu___187_11027  ->
                        match uu___187_11027 with
                        | UnfoldOnly uu____11028 -> false
                        | NoDeltaSteps  -> false
                        | uu____11031 -> true) cfg.steps in
                 {
                   steps = uu____11024;
                   tcenv = (uu___223_11023.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___223_11023.primitive_steps)
                 } in
               let uu____11032 = get_norm_request (norm cfg' env []) args in
               (match uu____11032 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11048 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___188_11053  ->
                                match uu___188_11053 with
                                | UnfoldUntil uu____11054 -> true
                                | UnfoldOnly uu____11055 -> true
                                | uu____11058 -> false)) in
                      if uu____11048
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___224_11063 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___224_11063.tcenv);
                        delta_level;
                        primitive_steps = (uu___224_11063.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11074 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11074
                      then
                        let uu____11077 =
                          let uu____11078 =
                            let uu____11083 = FStar_Util.now () in
                            (t1, uu____11083) in
                          Debug uu____11078 in
                        uu____11077 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11085;
                  FStar_Syntax_Syntax.vars = uu____11086;_},a1::a2::rest)
               ->
               let uu____11134 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11134 with
                | (hd1,uu____11150) ->
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
                    (FStar_Const.Const_reflect uu____11215);
                  FStar_Syntax_Syntax.pos = uu____11216;
                  FStar_Syntax_Syntax.vars = uu____11217;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11249 = FStar_List.tl stack1 in
               norm cfg env uu____11249 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11252;
                  FStar_Syntax_Syntax.vars = uu____11253;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11285 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11285 with
                | (reify_head,uu____11301) ->
                    let a1 =
                      let uu____11323 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11323 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11326);
                            FStar_Syntax_Syntax.pos = uu____11327;
                            FStar_Syntax_Syntax.vars = uu____11328;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11362 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11372 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11372
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11379 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11379
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11382 =
                      let uu____11389 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11389, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11382 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___189_11402  ->
                         match uu___189_11402 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11405 =
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
                 if uu____11405
                 then false
                 else
                   (let uu____11407 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___190_11414  ->
                              match uu___190_11414 with
                              | UnfoldOnly uu____11415 -> true
                              | uu____11418 -> false)) in
                    match uu____11407 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11422 -> should_delta) in
               (log cfg
                  (fun uu____11430  ->
                     let uu____11431 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11432 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11433 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11431 uu____11432 uu____11433);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11436 = lookup_bvar env x in
               (match uu____11436 with
                | Univ uu____11439 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11488 = FStar_ST.op_Bang r in
                      (match uu____11488 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11625  ->
                                 let uu____11626 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11627 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11626
                                   uu____11627);
                            (let uu____11628 =
                               let uu____11629 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11629.FStar_Syntax_Syntax.n in
                             match uu____11628 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11632 ->
                                 norm cfg env2 stack1 t'
                             | uu____11649 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11707)::uu____11708 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11717)::uu____11718 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11728,uu____11729))::stack_rest ->
                    (match c with
                     | Univ uu____11733 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11742 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11763  ->
                                    let uu____11764 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11764);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11804  ->
                                    let uu____11805 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11805);
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
                      (let uu___225_11855 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___225_11855.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11888  ->
                          let uu____11889 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11889);
                     norm cfg env stack2 t1)
                | (Debug uu____11890)::uu____11891 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11898 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11898
                    else
                      (let uu____11900 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11900 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11942  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11970 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11970
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11980 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11980)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_11985 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_11985.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_11985.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11986 -> lopt in
                           (log cfg
                              (fun uu____11992  ->
                                 let uu____11993 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11993);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12016)::uu____12017 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12024 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12024
                    else
                      (let uu____12026 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12026 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12068  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12096 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12096
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12106 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12106)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12111 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12111.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12111.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12112 -> lopt in
                           (log cfg
                              (fun uu____12118  ->
                                 let uu____12119 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12119);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12142)::uu____12143 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12154 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12154
                    else
                      (let uu____12156 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12156 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12198  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12226 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12226
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12236 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12236)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12241 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12241.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12241.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12242 -> lopt in
                           (log cfg
                              (fun uu____12248  ->
                                 let uu____12249 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12249);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12272)::uu____12273 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12284 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12284
                    else
                      (let uu____12286 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12286 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12328  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12356 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12356
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12366 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12366)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12371 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12371.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12371.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12372 -> lopt in
                           (log cfg
                              (fun uu____12378  ->
                                 let uu____12379 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12379);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12402)::uu____12403 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12418 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12418
                    else
                      (let uu____12420 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12420 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12462  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12490 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12490
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12500 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12500)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12505 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12505.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12505.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12506 -> lopt in
                           (log cfg
                              (fun uu____12512  ->
                                 let uu____12513 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12513);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12536 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12536
                    else
                      (let uu____12538 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12538 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12580  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12608 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12608
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12618 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12618)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12623 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12623.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12623.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12624 -> lopt in
                           (log cfg
                              (fun uu____12630  ->
                                 let uu____12631 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12631);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 = only_strong_steps cfg in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12692  ->
                         fun stack2  ->
                           match uu____12692 with
                           | (a,aq) ->
                               let uu____12704 =
                                 let uu____12705 =
                                   let uu____12712 =
                                     let uu____12713 =
                                       let uu____12744 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12744, false) in
                                     Clos uu____12713 in
                                   (uu____12712, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12705 in
                               uu____12704 :: stack2) args) in
               (log cfg
                  (fun uu____12820  ->
                     let uu____12821 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12821);
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
                             ((let uu___227_12857 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___227_12857.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___227_12857.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12858 ->
                      let uu____12863 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12863)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12866 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12866 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12897 =
                          let uu____12898 =
                            let uu____12905 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___228_12907 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___228_12907.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___228_12907.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12905) in
                          FStar_Syntax_Syntax.Tm_refine uu____12898 in
                        mk uu____12897 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12926 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12926
               else
                 (let uu____12928 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12928 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12936 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12960  -> dummy :: env1) env) in
                        norm_comp cfg uu____12936 c1 in
                      let t2 =
                        let uu____12982 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12982 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13041)::uu____13042 ->
                    (log cfg
                       (fun uu____13053  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13054)::uu____13055 ->
                    (log cfg
                       (fun uu____13066  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13067,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13068;
                                   FStar_Syntax_Syntax.vars = uu____13069;_},uu____13070,uu____13071))::uu____13072
                    ->
                    (log cfg
                       (fun uu____13081  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13082)::uu____13083 ->
                    (log cfg
                       (fun uu____13094  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13095 ->
                    (log cfg
                       (fun uu____13098  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13102  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13119 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13119
                         | FStar_Util.Inr c ->
                             let uu____13127 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13127 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13133 =
                         let uu____13134 =
                           let uu____13135 =
                             let uu____13162 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13162, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13135 in
                         mk uu____13134 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13133))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13238,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13239;
                               FStar_Syntax_Syntax.lbunivs = uu____13240;
                               FStar_Syntax_Syntax.lbtyp = uu____13241;
                               FStar_Syntax_Syntax.lbeff = uu____13242;
                               FStar_Syntax_Syntax.lbdef = uu____13243;_}::uu____13244),uu____13245)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13281 =
                 (let uu____13284 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13284) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13286 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13286))) in
               if uu____13281
               then
                 let binder =
                   let uu____13288 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13288 in
                 let env1 =
                   let uu____13298 =
                     let uu____13305 =
                       let uu____13306 =
                         let uu____13337 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13337,
                           false) in
                       Clos uu____13306 in
                     ((FStar_Pervasives_Native.Some binder), uu____13305) in
                   uu____13298 :: env in
                 (log cfg
                    (fun uu____13422  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13424 =
                    let uu____13429 =
                      let uu____13430 =
                        let uu____13431 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13431
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13430] in
                    FStar_Syntax_Subst.open_term uu____13429 body in
                  match uu____13424 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13440  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13448 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13448 in
                          FStar_Util.Inl
                            (let uu___229_13458 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___229_13458.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___229_13458.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13461  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___230_13463 = lb in
                           let uu____13464 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___230_13463.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___230_13463.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13464
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13499  -> dummy :: env1) env) in
                         let cfg1 = only_strong_steps cfg in
                         log cfg1
                           (fun uu____13521  ->
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
               let uu____13538 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13538 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13574 =
                               let uu___231_13575 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___231_13575.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___231_13575.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13574 in
                           let uu____13576 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13576 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13602 =
                                   FStar_List.map (fun uu____13618  -> dummy)
                                     lbs1 in
                                 let uu____13619 =
                                   let uu____13628 =
                                     FStar_List.map
                                       (fun uu____13648  -> dummy) xs1 in
                                   FStar_List.append uu____13628 env in
                                 FStar_List.append uu____13602 uu____13619 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13672 =
                                       let uu___232_13673 = rc in
                                       let uu____13674 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___232_13673.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13674;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___232_13673.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13672
                                 | uu____13681 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___233_13685 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___233_13685.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___233_13685.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13695 =
                        FStar_List.map (fun uu____13711  -> dummy) lbs2 in
                      FStar_List.append uu____13695 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13719 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13719 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___234_13735 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___234_13735.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___234_13735.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13762 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13762
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13781 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13857  ->
                        match uu____13857 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___235_13978 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___235_13978.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___235_13978.FStar_Syntax_Syntax.sort)
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
               (match uu____13781 with
                | (rec_env,memos,uu____14175) ->
                    let uu____14228 =
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
                             let uu____14759 =
                               let uu____14766 =
                                 let uu____14767 =
                                   let uu____14798 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14798, false) in
                                 Clos uu____14767 in
                               (FStar_Pervasives_Native.None, uu____14766) in
                             uu____14759 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14903 =
                      let uu____14904 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14904 in
                    if uu____14903
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14914 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14914
                        then
                          let uu___236_14915 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___236_14915.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___236_14915.primitive_steps)
                          }
                        else
                          (let uu___237_14917 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___237_14917.tcenv);
                             delta_level = (uu___237_14917.delta_level);
                             primitive_steps =
                               (uu___237_14917.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14919 =
                         let uu____14920 = FStar_Syntax_Subst.compress head1 in
                         uu____14920.FStar_Syntax_Syntax.n in
                       match uu____14919 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14938 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14938 with
                            | (uu____14939,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14945 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14953 =
                                         let uu____14954 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14954.FStar_Syntax_Syntax.n in
                                       match uu____14953 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14960,uu____14961))
                                           ->
                                           let uu____14970 =
                                             let uu____14971 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14971.FStar_Syntax_Syntax.n in
                                           (match uu____14970 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14977,msrc,uu____14979))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14988 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14988
                                            | uu____14989 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14990 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14991 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14991 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___238_14996 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___238_14996.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___238_14996.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___238_14996.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14997 =
                                            FStar_List.tl stack1 in
                                          let uu____14998 =
                                            let uu____14999 =
                                              let uu____15002 =
                                                let uu____15003 =
                                                  let uu____15016 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15016) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15003 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15002 in
                                            uu____14999
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14997
                                            uu____14998
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15032 =
                                            let uu____15033 = is_return body in
                                            match uu____15033 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15037;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15038;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15043 -> false in
                                          if uu____15032
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
                                               let uu____15067 =
                                                 let uu____15070 =
                                                   let uu____15071 =
                                                     let uu____15088 =
                                                       let uu____15091 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15091] in
                                                     (uu____15088, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15071 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15070 in
                                               uu____15067
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15107 =
                                                 let uu____15108 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15108.FStar_Syntax_Syntax.n in
                                               match uu____15107 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15114::uu____15115::[])
                                                   ->
                                                   let uu____15122 =
                                                     let uu____15125 =
                                                       let uu____15126 =
                                                         let uu____15133 =
                                                           let uu____15136 =
                                                             let uu____15137
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15137 in
                                                           let uu____15138 =
                                                             let uu____15141
                                                               =
                                                               let uu____15142
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15142 in
                                                             [uu____15141] in
                                                           uu____15136 ::
                                                             uu____15138 in
                                                         (bind1, uu____15133) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15126 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15125 in
                                                   uu____15122
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15150 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15156 =
                                                 let uu____15159 =
                                                   let uu____15160 =
                                                     let uu____15175 =
                                                       let uu____15178 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15179 =
                                                         let uu____15182 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15183 =
                                                           let uu____15186 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15187 =
                                                             let uu____15190
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15191
                                                               =
                                                               let uu____15194
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15195
                                                                 =
                                                                 let uu____15198
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15198] in
                                                               uu____15194 ::
                                                                 uu____15195 in
                                                             uu____15190 ::
                                                               uu____15191 in
                                                           uu____15186 ::
                                                             uu____15187 in
                                                         uu____15182 ::
                                                           uu____15183 in
                                                       uu____15178 ::
                                                         uu____15179 in
                                                     (bind_inst, uu____15175) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15160 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15159 in
                                               uu____15156
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15206 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15206 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15230 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15230 with
                            | (uu____15231,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15266 =
                                        let uu____15267 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15267.FStar_Syntax_Syntax.n in
                                      match uu____15266 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15273) -> t4
                                      | uu____15278 -> head2 in
                                    let uu____15279 =
                                      let uu____15280 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15280.FStar_Syntax_Syntax.n in
                                    match uu____15279 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15286 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15287 = maybe_extract_fv head2 in
                                  match uu____15287 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15297 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15297
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15302 =
                                          maybe_extract_fv head3 in
                                        match uu____15302 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15307 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15308 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15313 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15328 =
                                    match uu____15328 with
                                    | (e,q) ->
                                        let uu____15335 =
                                          let uu____15336 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15336.FStar_Syntax_Syntax.n in
                                        (match uu____15335 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15351 -> false) in
                                  let uu____15352 =
                                    let uu____15353 =
                                      let uu____15360 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15360 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15353 in
                                  if uu____15352
                                  then
                                    let uu____15365 =
                                      let uu____15366 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15366 in
                                    failwith uu____15365
                                  else ());
                                 (let uu____15368 =
                                    maybe_unfold_action head_app in
                                  match uu____15368 with
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
                                      let uu____15407 = FStar_List.tl stack1 in
                                      norm cfg env uu____15407 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15421 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15421 in
                           let uu____15422 = FStar_List.tl stack1 in
                           norm cfg env uu____15422 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15543  ->
                                     match uu____15543 with
                                     | (pat,wopt,tm) ->
                                         let uu____15591 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15591))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15623 = FStar_List.tl stack1 in
                           norm cfg env uu____15623 tm
                       | uu____15624 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15632 = should_reify cfg stack1 in
                    if uu____15632
                    then
                      let uu____15633 = FStar_List.tl stack1 in
                      let uu____15634 =
                        let uu____15635 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15635 in
                      norm cfg env uu____15633 uu____15634
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15638 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15638
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___239_15647 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___239_15647.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___239_15647.primitive_steps)
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
                | uu____15649 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15651::uu____15652 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15657) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15658 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15689 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15703 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15703
                             | uu____15714 -> m in
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
              let uu____15726 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15726 in
            let uu____15727 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15727 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15740  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15751  ->
                      let uu____15752 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15753 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15752
                        uu____15753);
                 (let t1 =
                    let uu____15755 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15755
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
                    | (UnivArgs (us',uu____15765))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____15820 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15823 ->
                        let uu____15826 =
                          let uu____15827 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15827 in
                        failwith uu____15826
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
              let uu____15837 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15837 with
              | (uu____15838,return_repr) ->
                  let return_inst =
                    let uu____15847 =
                      let uu____15848 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15848.FStar_Syntax_Syntax.n in
                    match uu____15847 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15854::[]) ->
                        let uu____15861 =
                          let uu____15864 =
                            let uu____15865 =
                              let uu____15872 =
                                let uu____15875 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15875] in
                              (return_tm, uu____15872) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15865 in
                          FStar_Syntax_Syntax.mk uu____15864 in
                        uu____15861 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15883 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15886 =
                    let uu____15889 =
                      let uu____15890 =
                        let uu____15905 =
                          let uu____15908 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15909 =
                            let uu____15912 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15912] in
                          uu____15908 :: uu____15909 in
                        (return_inst, uu____15905) in
                      FStar_Syntax_Syntax.Tm_app uu____15890 in
                    FStar_Syntax_Syntax.mk uu____15889 in
                  uu____15886 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15921 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15921 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15924 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15924
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15925;
                     FStar_TypeChecker_Env.mtarget = uu____15926;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15927;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15938;
                     FStar_TypeChecker_Env.mtarget = uu____15939;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15940;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15958 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15958)
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
                (fun uu____16014  ->
                   match uu____16014 with
                   | (a,imp) ->
                       let uu____16025 = norm cfg env [] a in
                       (uu____16025, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___240_16042 = comp1 in
            let uu____16045 =
              let uu____16046 =
                let uu____16055 = norm cfg env [] t in
                let uu____16056 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16055, uu____16056) in
              FStar_Syntax_Syntax.Total uu____16046 in
            {
              FStar_Syntax_Syntax.n = uu____16045;
              FStar_Syntax_Syntax.pos =
                (uu___240_16042.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___240_16042.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___241_16071 = comp1 in
            let uu____16074 =
              let uu____16075 =
                let uu____16084 = norm cfg env [] t in
                let uu____16085 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16084, uu____16085) in
              FStar_Syntax_Syntax.GTotal uu____16075 in
            {
              FStar_Syntax_Syntax.n = uu____16074;
              FStar_Syntax_Syntax.pos =
                (uu___241_16071.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___241_16071.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16137  ->
                      match uu____16137 with
                      | (a,i) ->
                          let uu____16148 = norm cfg env [] a in
                          (uu____16148, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___191_16159  ->
                      match uu___191_16159 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16163 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16163
                      | f -> f)) in
            let uu___242_16167 = comp1 in
            let uu____16170 =
              let uu____16171 =
                let uu___243_16172 = ct in
                let uu____16173 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16174 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16177 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16173;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___243_16172.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16174;
                  FStar_Syntax_Syntax.effect_args = uu____16177;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16171 in
            {
              FStar_Syntax_Syntax.n = uu____16170;
              FStar_Syntax_Syntax.pos =
                (uu___242_16167.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___242_16167.FStar_Syntax_Syntax.vars)
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
            (let uu___244_16195 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___244_16195.tcenv);
               delta_level = (uu___244_16195.delta_level);
               primitive_steps = (uu___244_16195.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____16200 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16200 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16203 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___245_16222 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___245_16222.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___245_16222.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16229 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16229
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
                    let uu___246_16240 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___246_16240.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___246_16240.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___246_16240.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___247_16242 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___247_16242.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___247_16242.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___247_16242.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___247_16242.FStar_Syntax_Syntax.flags)
                    } in
              let uu___248_16243 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___248_16243.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___248_16243.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16245 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16248  ->
        match uu____16248 with
        | (x,imp) ->
            let uu____16251 =
              let uu___249_16252 = x in
              let uu____16253 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___249_16252.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___249_16252.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16253
              } in
            (uu____16251, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16259 =
          FStar_List.fold_left
            (fun uu____16277  ->
               fun b  ->
                 match uu____16277 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16259 with | (nbs,uu____16317) -> FStar_List.rev nbs
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
            let uu____16333 =
              let uu___250_16334 = rc in
              let uu____16335 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___250_16334.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16335;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___250_16334.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16333
        | uu____16342 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16355  ->
               let uu____16356 = FStar_Syntax_Print.tag_of_term t in
               let uu____16357 = FStar_Syntax_Print.term_to_string t in
               let uu____16358 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16365 =
                 let uu____16366 =
                   let uu____16369 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16369 in
                 stack_to_string uu____16366 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16356 uu____16357 uu____16358 uu____16365);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16398 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16398
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16400 =
                     let uu____16401 =
                       let uu____16402 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16402 in
                     FStar_Util.string_of_int uu____16401 in
                   let uu____16407 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16408 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16400 uu____16407 uu____16408
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___251_16426 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___251_16426.tcenv);
                    delta_level = dl;
                    primitive_steps = ps
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16467  ->
                     let uu____16468 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16468);
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
               let uu____16504 =
                 let uu___252_16505 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___252_16505.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___252_16505.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16504
           | (Arg (Univ uu____16506,uu____16507,uu____16508))::uu____16509 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16512,uu____16513))::uu____16514 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16530),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16583  ->
                     let uu____16584 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16584);
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
                  (let uu____16594 = FStar_ST.op_Bang m in
                   match uu____16594 with
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
                   | FStar_Pervasives_Native.Some (uu____16738,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16781 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16781
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16793  ->
                     let uu____16794 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16794);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16799 =
                   log cfg
                     (fun uu____16804  ->
                        let uu____16805 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16806 =
                          let uu____16807 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16824  ->
                                    match uu____16824 with
                                    | (p,uu____16834,uu____16835) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16807
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16805 uu____16806);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___192_16852  ->
                                match uu___192_16852 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16853 -> false)) in
                      let steps' =
                        let uu____16857 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____16857
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      only_strong_steps
                        (let uu___253_16863 = cfg in
                         {
                           steps = (FStar_List.append steps' cfg.steps);
                           tcenv = (uu___253_16863.tcenv);
                           delta_level = new_delta;
                           primitive_steps = (uu___253_16863.primitive_steps)
                         }) in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16895 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16916 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16976  ->
                                    fun uu____16977  ->
                                      match (uu____16976, uu____16977) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17068 = norm_pat env3 p1 in
                                          (match uu____17068 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16916 with
                           | (pats1,env3) ->
                               ((let uu___254_17150 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___254_17150.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___255_17169 = x in
                            let uu____17170 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___255_17169.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___255_17169.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17170
                            } in
                          ((let uu___256_17184 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___256_17184.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___257_17195 = x in
                            let uu____17196 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___257_17195.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___257_17195.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17196
                            } in
                          ((let uu___258_17210 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___258_17210.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___259_17226 = x in
                            let uu____17227 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___259_17226.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___259_17226.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17227
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___260_17234 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___260_17234.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17244 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17258 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17258 with
                                  | (p,wopt,e) ->
                                      let uu____17278 = norm_pat env1 p in
                                      (match uu____17278 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17303 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17303 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17309 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17309) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17319) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17324 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17325;
                         FStar_Syntax_Syntax.fv_delta = uu____17326;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17327;
                         FStar_Syntax_Syntax.fv_delta = uu____17328;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17329);_}
                       -> true
                   | uu____17336 -> false in
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
                   let uu____17481 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17481 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17568 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____17607 ->
                                 let uu____17608 =
                                   let uu____17609 = is_cons head1 in
                                   Prims.op_Negation uu____17609 in
                                 FStar_Util.Inr uu____17608)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17634 =
                              let uu____17635 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17635.FStar_Syntax_Syntax.n in
                            (match uu____17634 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17653 ->
                                 let uu____17654 =
                                   let uu____17655 = is_cons head1 in
                                   Prims.op_Negation uu____17655 in
                                 FStar_Util.Inr uu____17654))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17724)::rest_a,(p1,uu____17727)::rest_p) ->
                       let uu____17771 = matches_pat t1 p1 in
                       (match uu____17771 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17820 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17926 = matches_pat scrutinee1 p1 in
                       (match uu____17926 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17966  ->
                                  let uu____17967 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17968 =
                                    let uu____17969 =
                                      FStar_List.map
                                        (fun uu____17979  ->
                                           match uu____17979 with
                                           | (uu____17984,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17969
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17967 uu____17968);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18015  ->
                                       match uu____18015 with
                                       | (bv,t1) ->
                                           let uu____18038 =
                                             let uu____18045 =
                                               let uu____18048 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18048 in
                                             let uu____18049 =
                                               let uu____18050 =
                                                 let uu____18081 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18081, false) in
                                               Clos uu____18050 in
                                             (uu____18045, uu____18049) in
                                           uu____18038 :: env2) env1 s in
                              let uu____18190 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18190))) in
                 let uu____18191 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18191
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___193_18214  ->
                match uu___193_18214 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18218 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18224 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps
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
            let uu___261_18253 = config s e in
            {
              steps = (uu___261_18253.steps);
              tcenv = (uu___261_18253.tcenv);
              delta_level = (uu___261_18253.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps)
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
      fun t  -> let uu____18284 = config s e in norm_comp uu____18284 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18299 = config [] env in norm_universe uu____18299 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18314 = config [] env in ghost_to_pure_aux uu____18314 [] c
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
        let uu____18334 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18334 in
      let uu____18341 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18341
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___262_18343 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___262_18343.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___262_18343.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18346  ->
                    let uu____18347 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18347))
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
            ((let uu____18366 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18366);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18379 = config [AllowUnboundUniverses] env in
          norm_comp uu____18379 [] c
        with
        | e ->
            ((let uu____18392 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18392);
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
                   let uu____18432 =
                     let uu____18433 =
                       let uu____18440 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18440) in
                     FStar_Syntax_Syntax.Tm_refine uu____18433 in
                   mk uu____18432 t01.FStar_Syntax_Syntax.pos
               | uu____18445 -> t2)
          | uu____18446 -> t2 in
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
        let uu____18498 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18498 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18527 ->
                 let uu____18534 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18534 with
                  | (actuals,uu____18544,uu____18545) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18559 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18559 with
                         | (binders,args) ->
                             let uu____18576 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18576
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
      | uu____18586 ->
          let uu____18587 = FStar_Syntax_Util.head_and_args t in
          (match uu____18587 with
           | (head1,args) ->
               let uu____18624 =
                 let uu____18625 = FStar_Syntax_Subst.compress head1 in
                 uu____18625.FStar_Syntax_Syntax.n in
               (match uu____18624 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18628,thead) ->
                    let uu____18654 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18654 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18696 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___267_18704 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___267_18704.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___267_18704.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___267_18704.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___267_18704.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___267_18704.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___267_18704.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___267_18704.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___267_18704.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___267_18704.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___267_18704.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___267_18704.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___267_18704.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___267_18704.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___267_18704.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___267_18704.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___267_18704.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___267_18704.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___267_18704.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___267_18704.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___267_18704.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___267_18704.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___267_18704.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___267_18704.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___267_18704.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___267_18704.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___267_18704.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___267_18704.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___267_18704.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___267_18704.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___267_18704.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____18696 with
                            | (uu____18705,ty,uu____18707) ->
                                eta_expand_with_type env t ty))
                | uu____18708 ->
                    let uu____18709 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___268_18717 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___268_18717.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___268_18717.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___268_18717.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___268_18717.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___268_18717.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___268_18717.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___268_18717.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___268_18717.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___268_18717.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___268_18717.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___268_18717.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___268_18717.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___268_18717.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___268_18717.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___268_18717.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___268_18717.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___268_18717.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___268_18717.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___268_18717.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___268_18717.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___268_18717.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___268_18717.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___268_18717.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___268_18717.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___268_18717.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___268_18717.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___268_18717.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___268_18717.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___268_18717.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___268_18717.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____18709 with
                     | (uu____18718,ty,uu____18720) ->
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
            | (uu____18798,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18804,FStar_Util.Inl t) ->
                let uu____18810 =
                  let uu____18813 =
                    let uu____18814 =
                      let uu____18827 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18827) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18814 in
                  FStar_Syntax_Syntax.mk uu____18813 in
                uu____18810 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18831 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18831 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18858 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18913 ->
                    let uu____18914 =
                      let uu____18923 =
                        let uu____18924 = FStar_Syntax_Subst.compress t3 in
                        uu____18924.FStar_Syntax_Syntax.n in
                      (uu____18923, tc) in
                    (match uu____18914 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18949) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18986) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19025,FStar_Util.Inl uu____19026) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19049 -> failwith "Impossible") in
              (match uu____18858 with
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
          let uu____19158 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19158 with
          | (univ_names1,binders1,tc) ->
              let uu____19216 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19216)
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
          let uu____19255 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19255 with
          | (univ_names1,binders1,tc) ->
              let uu____19315 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19315)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19350 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19350 with
           | (univ_names1,binders1,typ1) ->
               let uu___269_19378 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___269_19378.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___269_19378.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___269_19378.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___269_19378.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___270_19399 = s in
          let uu____19400 =
            let uu____19401 =
              let uu____19410 = FStar_List.map (elim_uvars env) sigs in
              (uu____19410, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19401 in
          {
            FStar_Syntax_Syntax.sigel = uu____19400;
            FStar_Syntax_Syntax.sigrng =
              (uu___270_19399.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___270_19399.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___270_19399.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___270_19399.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19427 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19427 with
           | (univ_names1,uu____19445,typ1) ->
               let uu___271_19459 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___271_19459.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___271_19459.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___271_19459.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___271_19459.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19465 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19465 with
           | (univ_names1,uu____19483,typ1) ->
               let uu___272_19497 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___272_19497.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___272_19497.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___272_19497.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___272_19497.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19531 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19531 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19554 =
                            let uu____19555 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19555 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19554 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___273_19558 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___273_19558.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___273_19558.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___274_19559 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___274_19559.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___274_19559.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___274_19559.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___274_19559.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___275_19571 = s in
          let uu____19572 =
            let uu____19573 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19573 in
          {
            FStar_Syntax_Syntax.sigel = uu____19572;
            FStar_Syntax_Syntax.sigrng =
              (uu___275_19571.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___275_19571.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___275_19571.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___275_19571.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19577 = elim_uvars_aux_t env us [] t in
          (match uu____19577 with
           | (us1,uu____19595,t1) ->
               let uu___276_19609 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___276_19609.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___276_19609.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___276_19609.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___276_19609.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19610 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19612 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19612 with
           | (univs1,binders,signature) ->
               let uu____19640 =
                 let uu____19649 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19649 with
                 | (univs_opening,univs2) ->
                     let uu____19676 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19676) in
               (match uu____19640 with
                | (univs_opening,univs_closing) ->
                    let uu____19693 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19699 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19700 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19699, uu____19700) in
                    (match uu____19693 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19722 =
                           match uu____19722 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19740 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19740 with
                                | (us1,t1) ->
                                    let uu____19751 =
                                      let uu____19756 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19763 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19756, uu____19763) in
                                    (match uu____19751 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19776 =
                                           let uu____19781 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19790 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19781, uu____19790) in
                                         (match uu____19776 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19806 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19806 in
                                              let uu____19807 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19807 with
                                               | (uu____19828,uu____19829,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19844 =
                                                       let uu____19845 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19845 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19844 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19850 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19850 with
                           | (uu____19863,uu____19864,t1) -> t1 in
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
                             | uu____19924 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19941 =
                               let uu____19942 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19942.FStar_Syntax_Syntax.n in
                             match uu____19941 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20001 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20030 =
                               let uu____20031 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20031.FStar_Syntax_Syntax.n in
                             match uu____20030 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20052) ->
                                 let uu____20073 = destruct_action_body body in
                                 (match uu____20073 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20118 ->
                                 let uu____20119 = destruct_action_body t in
                                 (match uu____20119 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20168 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20168 with
                           | (action_univs,t) ->
                               let uu____20177 = destruct_action_typ_templ t in
                               (match uu____20177 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___277_20218 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___277_20218.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___277_20218.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___278_20220 = ed in
                           let uu____20221 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20222 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20223 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20224 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20225 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20226 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20227 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20228 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20229 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20230 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20231 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20232 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20233 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20234 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___278_20220.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___278_20220.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20221;
                             FStar_Syntax_Syntax.bind_wp = uu____20222;
                             FStar_Syntax_Syntax.if_then_else = uu____20223;
                             FStar_Syntax_Syntax.ite_wp = uu____20224;
                             FStar_Syntax_Syntax.stronger = uu____20225;
                             FStar_Syntax_Syntax.close_wp = uu____20226;
                             FStar_Syntax_Syntax.assert_p = uu____20227;
                             FStar_Syntax_Syntax.assume_p = uu____20228;
                             FStar_Syntax_Syntax.null_wp = uu____20229;
                             FStar_Syntax_Syntax.trivial = uu____20230;
                             FStar_Syntax_Syntax.repr = uu____20231;
                             FStar_Syntax_Syntax.return_repr = uu____20232;
                             FStar_Syntax_Syntax.bind_repr = uu____20233;
                             FStar_Syntax_Syntax.actions = uu____20234
                           } in
                         let uu___279_20237 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___279_20237.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___279_20237.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___279_20237.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___279_20237.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___194_20254 =
            match uu___194_20254 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20281 = elim_uvars_aux_t env us [] t in
                (match uu____20281 with
                 | (us1,uu____20305,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___280_20324 = sub_eff in
            let uu____20325 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20328 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___280_20324.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___280_20324.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20325;
              FStar_Syntax_Syntax.lift = uu____20328
            } in
          let uu___281_20331 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___281_20331.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___281_20331.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___281_20331.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___281_20331.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20341 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20341 with
           | (univ_names1,binders1,comp1) ->
               let uu___282_20375 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___282_20375.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___282_20375.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___282_20375.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___282_20375.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20386 -> s