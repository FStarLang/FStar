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
                                else reduce_equality cfg env stack1 tm1)))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8781;
                    FStar_Syntax_Syntax.vars = uu____8782;_},args)
                 ->
                 let uu____8804 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8804
                 then
                   let uu____8805 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8805 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8860)::
                        (uu____8861,(arg,uu____8863))::[] -> arg
                    | (uu____8928,(arg,uu____8930))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8931)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8996)::uu____8997::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9060::(FStar_Pervasives_Native.Some (false
                                   ),uu____9061)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9124 -> tm1)
                 else
                   (let uu____9140 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9140
                    then
                      let uu____9141 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9141 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9196)::uu____9197::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9260::(FStar_Pervasives_Native.Some (true
                                     ),uu____9261)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9324)::
                          (uu____9325,(arg,uu____9327))::[] -> arg
                      | (uu____9392,(arg,uu____9394))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9395)::[]
                          -> arg
                      | uu____9460 -> tm1
                    else
                      (let uu____9476 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9476
                       then
                         let uu____9477 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9477 with
                         | uu____9532::(FStar_Pervasives_Native.Some (true
                                        ),uu____9533)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9596)::uu____9597::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9660)::
                             (uu____9661,(arg,uu____9663))::[] -> arg
                         | (uu____9728,(p,uu____9730))::(uu____9731,(q,uu____9733))::[]
                             ->
                             let uu____9798 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9798
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9800 -> tm1
                       else
                         (let uu____9816 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9816
                          then
                            let uu____9817 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9817 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9872)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9911)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9950 -> tm1
                          else
                            (let uu____9966 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9966
                             then
                               match args with
                               | (t,uu____9968)::[] ->
                                   let uu____9985 =
                                     let uu____9986 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9986.FStar_Syntax_Syntax.n in
                                   (match uu____9985 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9989::[],body,uu____9991) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10018 -> tm1)
                                    | uu____10021 -> tm1)
                               | (uu____10022,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10023))::
                                   (t,uu____10025)::[] ->
                                   let uu____10064 =
                                     let uu____10065 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10065.FStar_Syntax_Syntax.n in
                                   (match uu____10064 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10068::[],body,uu____10070) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10097 -> tm1)
                                    | uu____10100 -> tm1)
                               | uu____10101 -> tm1
                             else
                               (let uu____10111 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10111
                                then
                                  match args with
                                  | (t,uu____10113)::[] ->
                                      let uu____10130 =
                                        let uu____10131 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10131.FStar_Syntax_Syntax.n in
                                      (match uu____10130 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10134::[],body,uu____10136)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10163 -> tm1)
                                       | uu____10166 -> tm1)
                                  | (uu____10167,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10168))::(t,uu____10170)::[] ->
                                      let uu____10209 =
                                        let uu____10210 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10210.FStar_Syntax_Syntax.n in
                                      (match uu____10209 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10213::[],body,uu____10215)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10242 -> tm1)
                                       | uu____10245 -> tm1)
                                  | uu____10246 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | uu____10256 -> tm1)
let is_norm_request:
  'Auu____10263 .
    FStar_Syntax_Syntax.term -> 'Auu____10263 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10276 =
        let uu____10283 =
          let uu____10284 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10284.FStar_Syntax_Syntax.n in
        (uu____10283, args) in
      match uu____10276 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10290::uu____10291::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10295::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10300::uu____10301::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10304 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___185_10316  ->
    match uu___185_10316 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10322 =
          let uu____10325 =
            let uu____10326 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10326 in
          [uu____10325] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10322
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10345 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10345) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10383 =
          let uu____10386 =
            let uu____10391 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10391 s in
          FStar_All.pipe_right uu____10386 FStar_Util.must in
        FStar_All.pipe_right uu____10383 tr_norm_steps in
      match args with
      | uu____10416::(tm,uu____10418)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10441)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10456)::uu____10457::(tm,uu____10459)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10499 =
              let uu____10502 = full_norm steps in parse_steps uu____10502 in
            Beta :: uu____10499 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10511 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___186_10529  ->
    match uu___186_10529 with
    | (App
        (uu____10532,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10533;
                       FStar_Syntax_Syntax.vars = uu____10534;_},uu____10535,uu____10536))::uu____10537
        -> true
    | uu____10544 -> false
let firstn:
  'Auu____10553 .
    Prims.int ->
      'Auu____10553 Prims.list ->
        ('Auu____10553 Prims.list,'Auu____10553 Prims.list)
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
          (uu____10591,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10592;
                         FStar_Syntax_Syntax.vars = uu____10593;_},uu____10594,uu____10595))::uu____10596
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10603 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10719  ->
               let uu____10720 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10721 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10722 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10729 =
                 let uu____10730 =
                   let uu____10733 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10733 in
                 stack_to_string uu____10730 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10720 uu____10721 uu____10722 uu____10729);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10756 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10781 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10798 =
                 let uu____10799 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10800 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10799 uu____10800 in
               failwith uu____10798
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10801 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10818 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10819 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10820;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10821;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10824;
                 FStar_Syntax_Syntax.fv_delta = uu____10825;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10826;
                 FStar_Syntax_Syntax.fv_delta = uu____10827;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10828);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10836 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10836 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10842  ->
                     let uu____10843 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10844 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10843 uu____10844);
                if b
                then
                  (let uu____10845 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10845 t1 fv)
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
                 let uu___222_10884 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___222_10884.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___222_10884.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10917 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10917) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___223_10925 = cfg in
                 let uu____10926 =
                   FStar_List.filter
                     (fun uu___187_10929  ->
                        match uu___187_10929 with
                        | UnfoldOnly uu____10930 -> false
                        | NoDeltaSteps  -> false
                        | uu____10933 -> true) cfg.steps in
                 {
                   steps = uu____10926;
                   tcenv = (uu___223_10925.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___223_10925.primitive_steps)
                 } in
               let uu____10934 = get_norm_request (norm cfg' env []) args in
               (match uu____10934 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10950 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___188_10955  ->
                                match uu___188_10955 with
                                | UnfoldUntil uu____10956 -> true
                                | UnfoldOnly uu____10957 -> true
                                | uu____10960 -> false)) in
                      if uu____10950
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___224_10965 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___224_10965.tcenv);
                        delta_level;
                        primitive_steps = (uu___224_10965.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10976 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10976
                      then
                        let uu____10979 =
                          let uu____10980 =
                            let uu____10985 = FStar_Util.now () in
                            (t1, uu____10985) in
                          Debug uu____10980 in
                        uu____10979 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10987;
                  FStar_Syntax_Syntax.vars = uu____10988;_},a1::a2::rest)
               ->
               let uu____11036 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11036 with
                | (hd1,uu____11052) ->
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
                    (FStar_Const.Const_reflect uu____11117);
                  FStar_Syntax_Syntax.pos = uu____11118;
                  FStar_Syntax_Syntax.vars = uu____11119;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11151 = FStar_List.tl stack1 in
               norm cfg env uu____11151 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11154;
                  FStar_Syntax_Syntax.vars = uu____11155;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11187 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11187 with
                | (reify_head,uu____11203) ->
                    let a1 =
                      let uu____11225 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11225 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11228);
                            FStar_Syntax_Syntax.pos = uu____11229;
                            FStar_Syntax_Syntax.vars = uu____11230;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11264 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11274 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11274
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11281 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11281
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11284 =
                      let uu____11291 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11291, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11284 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___189_11304  ->
                         match uu___189_11304 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11307 =
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
                 if uu____11307
                 then false
                 else
                   (let uu____11309 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___190_11316  ->
                              match uu___190_11316 with
                              | UnfoldOnly uu____11317 -> true
                              | uu____11320 -> false)) in
                    match uu____11309 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11324 -> should_delta) in
               (log cfg
                  (fun uu____11332  ->
                     let uu____11333 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11334 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11335 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11333 uu____11334 uu____11335);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11338 = lookup_bvar env x in
               (match uu____11338 with
                | Univ uu____11341 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11390 = FStar_ST.op_Bang r in
                      (match uu____11390 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11527  ->
                                 let uu____11528 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11529 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11528
                                   uu____11529);
                            (let uu____11530 =
                               let uu____11531 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11531.FStar_Syntax_Syntax.n in
                             match uu____11530 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11534 ->
                                 norm cfg env2 stack1 t'
                             | uu____11551 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11609)::uu____11610 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11619)::uu____11620 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11630,uu____11631))::stack_rest ->
                    (match c with
                     | Univ uu____11635 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11644 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11665  ->
                                    let uu____11666 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11666);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11706  ->
                                    let uu____11707 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11707);
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
                      (let uu___225_11757 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___225_11757.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11790  ->
                          let uu____11791 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11791);
                     norm cfg env stack2 t1)
                | (Debug uu____11792)::uu____11793 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11800 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11800
                    else
                      (let uu____11802 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11802 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11844  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11872 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11872
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11882 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11882)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_11887 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_11887.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_11887.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11888 -> lopt in
                           (log cfg
                              (fun uu____11894  ->
                                 let uu____11895 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11895);
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
                | (Meta uu____11918)::uu____11919 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11926 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11926
                    else
                      (let uu____11928 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11928 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11970  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11998 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11998
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12008 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12008)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12013 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12013.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12013.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12014 -> lopt in
                           (log cfg
                              (fun uu____12020  ->
                                 let uu____12021 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12021);
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
                | (Let uu____12044)::uu____12045 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12056 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12056
                    else
                      (let uu____12058 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12058 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12100  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12128 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12128
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12138 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12138)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12143 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12143.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12143.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12144 -> lopt in
                           (log cfg
                              (fun uu____12150  ->
                                 let uu____12151 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12151);
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
                | (App uu____12174)::uu____12175 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12186 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12186
                    else
                      (let uu____12188 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12188 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12230  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12258 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12258
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12268 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12268)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12273 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12273.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12273.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12274 -> lopt in
                           (log cfg
                              (fun uu____12280  ->
                                 let uu____12281 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12281);
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
                | (Abs uu____12304)::uu____12305 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12320 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12320
                    else
                      (let uu____12322 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12322 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12364  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12392 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12392
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12402 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12402)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12407 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12407.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12407.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12408 -> lopt in
                           (log cfg
                              (fun uu____12414  ->
                                 let uu____12415 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12415);
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
                      let uu____12438 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12438
                    else
                      (let uu____12440 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12440 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12482  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12510 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12510
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12520 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12520)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12525 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12525.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12525.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12526 -> lopt in
                           (log cfg
                              (fun uu____12532  ->
                                 let uu____12533 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12533);
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
                      (fun uu____12594  ->
                         fun stack2  ->
                           match uu____12594 with
                           | (a,aq) ->
                               let uu____12606 =
                                 let uu____12607 =
                                   let uu____12614 =
                                     let uu____12615 =
                                       let uu____12646 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12646, false) in
                                     Clos uu____12615 in
                                   (uu____12614, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12607 in
                               uu____12606 :: stack2) args) in
               (log cfg
                  (fun uu____12722  ->
                     let uu____12723 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12723);
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
                             ((let uu___227_12759 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___227_12759.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___227_12759.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12760 ->
                      let uu____12765 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12765)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12768 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12768 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12799 =
                          let uu____12800 =
                            let uu____12807 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___228_12809 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___228_12809.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___228_12809.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12807) in
                          FStar_Syntax_Syntax.Tm_refine uu____12800 in
                        mk uu____12799 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12828 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12828
               else
                 (let uu____12830 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12830 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12838 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12862  -> dummy :: env1) env) in
                        norm_comp cfg uu____12838 c1 in
                      let t2 =
                        let uu____12884 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12884 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12943)::uu____12944 ->
                    (log cfg
                       (fun uu____12955  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____12956)::uu____12957 ->
                    (log cfg
                       (fun uu____12968  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____12969,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12970;
                                   FStar_Syntax_Syntax.vars = uu____12971;_},uu____12972,uu____12973))::uu____12974
                    ->
                    (log cfg
                       (fun uu____12983  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____12984)::uu____12985 ->
                    (log cfg
                       (fun uu____12996  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____12997 ->
                    (log cfg
                       (fun uu____13000  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13004  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13021 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13021
                         | FStar_Util.Inr c ->
                             let uu____13029 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13029 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13035 =
                         let uu____13036 =
                           let uu____13037 =
                             let uu____13064 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13064, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13037 in
                         mk uu____13036 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13035))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13140,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13141;
                               FStar_Syntax_Syntax.lbunivs = uu____13142;
                               FStar_Syntax_Syntax.lbtyp = uu____13143;
                               FStar_Syntax_Syntax.lbeff = uu____13144;
                               FStar_Syntax_Syntax.lbdef = uu____13145;_}::uu____13146),uu____13147)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13183 =
                 (let uu____13186 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13186) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13188 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13188))) in
               if uu____13183
               then
                 let binder =
                   let uu____13190 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13190 in
                 let env1 =
                   let uu____13200 =
                     let uu____13207 =
                       let uu____13208 =
                         let uu____13239 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13239,
                           false) in
                       Clos uu____13208 in
                     ((FStar_Pervasives_Native.Some binder), uu____13207) in
                   uu____13200 :: env in
                 (log cfg
                    (fun uu____13324  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13326 =
                    let uu____13331 =
                      let uu____13332 =
                        let uu____13333 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13333
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13332] in
                    FStar_Syntax_Subst.open_term uu____13331 body in
                  match uu____13326 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13342  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13350 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13350 in
                          FStar_Util.Inl
                            (let uu___229_13360 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___229_13360.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___229_13360.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13363  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___230_13365 = lb in
                           let uu____13366 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___230_13365.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___230_13365.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13366
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13401  -> dummy :: env1) env) in
                         let cfg1 = only_strong_steps cfg in
                         log cfg1
                           (fun uu____13423  ->
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
               let uu____13440 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13440 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13476 =
                               let uu___231_13477 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___231_13477.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___231_13477.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13476 in
                           let uu____13478 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13478 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13504 =
                                   FStar_List.map (fun uu____13520  -> dummy)
                                     lbs1 in
                                 let uu____13521 =
                                   let uu____13530 =
                                     FStar_List.map
                                       (fun uu____13550  -> dummy) xs1 in
                                   FStar_List.append uu____13530 env in
                                 FStar_List.append uu____13504 uu____13521 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13574 =
                                       let uu___232_13575 = rc in
                                       let uu____13576 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___232_13575.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13576;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___232_13575.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13574
                                 | uu____13583 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___233_13587 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___233_13587.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___233_13587.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13597 =
                        FStar_List.map (fun uu____13613  -> dummy) lbs2 in
                      FStar_List.append uu____13597 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13621 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13621 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___234_13637 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___234_13637.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___234_13637.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13664 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13664
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13683 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13759  ->
                        match uu____13759 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___235_13880 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___235_13880.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___235_13880.FStar_Syntax_Syntax.sort)
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
               (match uu____13683 with
                | (rec_env,memos,uu____14077) ->
                    let uu____14130 =
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
                             let uu____14661 =
                               let uu____14668 =
                                 let uu____14669 =
                                   let uu____14700 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14700, false) in
                                 Clos uu____14669 in
                               (FStar_Pervasives_Native.None, uu____14668) in
                             uu____14661 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____14805 =
                      let uu____14806 = should_reify cfg stack1 in
                      Prims.op_Negation uu____14806 in
                    if uu____14805
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14816 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14816
                        then
                          let uu___236_14817 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___236_14817.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___236_14817.primitive_steps)
                          }
                        else
                          (let uu___237_14819 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___237_14819.tcenv);
                             delta_level = (uu___237_14819.delta_level);
                             primitive_steps =
                               (uu___237_14819.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14821 =
                         let uu____14822 = FStar_Syntax_Subst.compress head1 in
                         uu____14822.FStar_Syntax_Syntax.n in
                       match uu____14821 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14840 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14840 with
                            | (uu____14841,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14847 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14855 =
                                         let uu____14856 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14856.FStar_Syntax_Syntax.n in
                                       match uu____14855 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14862,uu____14863))
                                           ->
                                           let uu____14872 =
                                             let uu____14873 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14873.FStar_Syntax_Syntax.n in
                                           (match uu____14872 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14879,msrc,uu____14881))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14890 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14890
                                            | uu____14891 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14892 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14893 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14893 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___238_14898 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___238_14898.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___238_14898.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___238_14898.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14899 =
                                            FStar_List.tl stack1 in
                                          let uu____14900 =
                                            let uu____14901 =
                                              let uu____14904 =
                                                let uu____14905 =
                                                  let uu____14918 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14918) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14905 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14904 in
                                            uu____14901
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14899
                                            uu____14900
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14934 =
                                            let uu____14935 = is_return body in
                                            match uu____14935 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14939;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14940;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14945 -> false in
                                          if uu____14934
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
                                               let uu____14969 =
                                                 let uu____14972 =
                                                   let uu____14973 =
                                                     let uu____14990 =
                                                       let uu____14993 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14993] in
                                                     (uu____14990, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14973 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14972 in
                                               uu____14969
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15009 =
                                                 let uu____15010 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15010.FStar_Syntax_Syntax.n in
                                               match uu____15009 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15016::uu____15017::[])
                                                   ->
                                                   let uu____15024 =
                                                     let uu____15027 =
                                                       let uu____15028 =
                                                         let uu____15035 =
                                                           let uu____15038 =
                                                             let uu____15039
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15039 in
                                                           let uu____15040 =
                                                             let uu____15043
                                                               =
                                                               let uu____15044
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15044 in
                                                             [uu____15043] in
                                                           uu____15038 ::
                                                             uu____15040 in
                                                         (bind1, uu____15035) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15028 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15027 in
                                                   uu____15024
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15052 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15058 =
                                                 let uu____15061 =
                                                   let uu____15062 =
                                                     let uu____15077 =
                                                       let uu____15080 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15081 =
                                                         let uu____15084 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15085 =
                                                           let uu____15088 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15089 =
                                                             let uu____15092
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15093
                                                               =
                                                               let uu____15096
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15097
                                                                 =
                                                                 let uu____15100
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15100] in
                                                               uu____15096 ::
                                                                 uu____15097 in
                                                             uu____15092 ::
                                                               uu____15093 in
                                                           uu____15088 ::
                                                             uu____15089 in
                                                         uu____15084 ::
                                                           uu____15085 in
                                                       uu____15080 ::
                                                         uu____15081 in
                                                     (bind_inst, uu____15077) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15062 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15061 in
                                               uu____15058
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15108 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15108 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15132 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15132 with
                            | (uu____15133,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15168 =
                                        let uu____15169 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15169.FStar_Syntax_Syntax.n in
                                      match uu____15168 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15175) -> t4
                                      | uu____15180 -> head2 in
                                    let uu____15181 =
                                      let uu____15182 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15182.FStar_Syntax_Syntax.n in
                                    match uu____15181 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15188 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15189 = maybe_extract_fv head2 in
                                  match uu____15189 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15199 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15199
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15204 =
                                          maybe_extract_fv head3 in
                                        match uu____15204 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15209 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15210 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15215 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15230 =
                                    match uu____15230 with
                                    | (e,q) ->
                                        let uu____15237 =
                                          let uu____15238 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15238.FStar_Syntax_Syntax.n in
                                        (match uu____15237 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15253 -> false) in
                                  let uu____15254 =
                                    let uu____15255 =
                                      let uu____15262 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15262 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15255 in
                                  if uu____15254
                                  then
                                    let uu____15267 =
                                      let uu____15268 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15268 in
                                    failwith uu____15267
                                  else ());
                                 (let uu____15270 =
                                    maybe_unfold_action head_app in
                                  match uu____15270 with
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
                                      let uu____15309 = FStar_List.tl stack1 in
                                      norm cfg env uu____15309 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15323 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15323 in
                           let uu____15324 = FStar_List.tl stack1 in
                           norm cfg env uu____15324 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15445  ->
                                     match uu____15445 with
                                     | (pat,wopt,tm) ->
                                         let uu____15493 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15493))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15525 = FStar_List.tl stack1 in
                           norm cfg env uu____15525 tm
                       | uu____15526 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15534 = should_reify cfg stack1 in
                    if uu____15534
                    then
                      let uu____15535 = FStar_List.tl stack1 in
                      let uu____15536 =
                        let uu____15537 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15537 in
                      norm cfg env uu____15535 uu____15536
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15540 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15540
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___239_15549 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___239_15549.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___239_15549.primitive_steps)
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
                | uu____15551 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15553::uu____15554 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15559) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15560 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15591 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15605 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15605
                             | uu____15616 -> m in
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
              let uu____15628 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15628 in
            let uu____15629 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15629 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15642  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15653  ->
                      let uu____15654 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15655 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15654
                        uu____15655);
                 (let t1 =
                    let uu____15657 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15657
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
                    | (UnivArgs (us',uu____15667))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____15722 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15725 ->
                        let uu____15728 =
                          let uu____15729 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15729 in
                        failwith uu____15728
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
              let uu____15739 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____15739 with
              | (uu____15740,return_repr) ->
                  let return_inst =
                    let uu____15749 =
                      let uu____15750 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____15750.FStar_Syntax_Syntax.n in
                    match uu____15749 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____15756::[]) ->
                        let uu____15763 =
                          let uu____15766 =
                            let uu____15767 =
                              let uu____15774 =
                                let uu____15777 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____15777] in
                              (return_tm, uu____15774) in
                            FStar_Syntax_Syntax.Tm_uinst uu____15767 in
                          FStar_Syntax_Syntax.mk uu____15766 in
                        uu____15763 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____15785 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____15788 =
                    let uu____15791 =
                      let uu____15792 =
                        let uu____15807 =
                          let uu____15810 = FStar_Syntax_Syntax.as_arg t in
                          let uu____15811 =
                            let uu____15814 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15814] in
                          uu____15810 :: uu____15811 in
                        (return_inst, uu____15807) in
                      FStar_Syntax_Syntax.Tm_app uu____15792 in
                    FStar_Syntax_Syntax.mk uu____15791 in
                  uu____15788 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____15823 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15823 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15826 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15826
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15827;
                     FStar_TypeChecker_Env.mtarget = uu____15828;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15829;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15840;
                     FStar_TypeChecker_Env.mtarget = uu____15841;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15842;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15860 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15860)
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
                (fun uu____15916  ->
                   match uu____15916 with
                   | (a,imp) ->
                       let uu____15927 = norm cfg env [] a in
                       (uu____15927, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___240_15944 = comp1 in
            let uu____15947 =
              let uu____15948 =
                let uu____15957 = norm cfg env [] t in
                let uu____15958 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15957, uu____15958) in
              FStar_Syntax_Syntax.Total uu____15948 in
            {
              FStar_Syntax_Syntax.n = uu____15947;
              FStar_Syntax_Syntax.pos =
                (uu___240_15944.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___240_15944.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___241_15973 = comp1 in
            let uu____15976 =
              let uu____15977 =
                let uu____15986 = norm cfg env [] t in
                let uu____15987 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15986, uu____15987) in
              FStar_Syntax_Syntax.GTotal uu____15977 in
            {
              FStar_Syntax_Syntax.n = uu____15976;
              FStar_Syntax_Syntax.pos =
                (uu___241_15973.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___241_15973.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16039  ->
                      match uu____16039 with
                      | (a,i) ->
                          let uu____16050 = norm cfg env [] a in
                          (uu____16050, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___191_16061  ->
                      match uu___191_16061 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16065 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16065
                      | f -> f)) in
            let uu___242_16069 = comp1 in
            let uu____16072 =
              let uu____16073 =
                let uu___243_16074 = ct in
                let uu____16075 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16076 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16079 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16075;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___243_16074.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16076;
                  FStar_Syntax_Syntax.effect_args = uu____16079;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16073 in
            {
              FStar_Syntax_Syntax.n = uu____16072;
              FStar_Syntax_Syntax.pos =
                (uu___242_16069.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___242_16069.FStar_Syntax_Syntax.vars)
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
            (let uu___244_16097 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___244_16097.tcenv);
               delta_level = (uu___244_16097.delta_level);
               primitive_steps = (uu___244_16097.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____16102 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16102 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16105 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___245_16124 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___245_16124.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___245_16124.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16131 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16131
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
                    let uu___246_16142 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___246_16142.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___246_16142.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___246_16142.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___247_16144 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___247_16144.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___247_16144.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___247_16144.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___247_16144.FStar_Syntax_Syntax.flags)
                    } in
              let uu___248_16145 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___248_16145.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___248_16145.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16147 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16150  ->
        match uu____16150 with
        | (x,imp) ->
            let uu____16153 =
              let uu___249_16154 = x in
              let uu____16155 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___249_16154.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___249_16154.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16155
              } in
            (uu____16153, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16161 =
          FStar_List.fold_left
            (fun uu____16179  ->
               fun b  ->
                 match uu____16179 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16161 with | (nbs,uu____16219) -> FStar_List.rev nbs
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
            let uu____16235 =
              let uu___250_16236 = rc in
              let uu____16237 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___250_16236.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16237;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___250_16236.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16235
        | uu____16244 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16257  ->
               let uu____16258 = FStar_Syntax_Print.tag_of_term t in
               let uu____16259 = FStar_Syntax_Print.term_to_string t in
               let uu____16260 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16267 =
                 let uu____16268 =
                   let uu____16271 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16271 in
                 stack_to_string uu____16268 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16258 uu____16259 uu____16260 uu____16267);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16300 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16300
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16302 =
                     let uu____16303 =
                       let uu____16304 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16304 in
                     FStar_Util.string_of_int uu____16303 in
                   let uu____16309 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16310 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16302 uu____16309 uu____16310
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___251_16328 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___251_16328.tcenv);
                    delta_level = dl;
                    primitive_steps = ps
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16369  ->
                     let uu____16370 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16370);
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
               let uu____16406 =
                 let uu___252_16407 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___252_16407.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___252_16407.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16406
           | (Arg (Univ uu____16408,uu____16409,uu____16410))::uu____16411 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16414,uu____16415))::uu____16416 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16432),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16485  ->
                     let uu____16486 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16486);
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
                  (let uu____16496 = FStar_ST.op_Bang m in
                   match uu____16496 with
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
                   | FStar_Pervasives_Native.Some (uu____16640,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16683 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16683
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16695  ->
                     let uu____16696 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16696);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16701 =
                   log cfg
                     (fun uu____16706  ->
                        let uu____16707 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16708 =
                          let uu____16709 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16726  ->
                                    match uu____16726 with
                                    | (p,uu____16736,uu____16737) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16709
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16707 uu____16708);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___192_16754  ->
                                match uu___192_16754 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16755 -> false)) in
                      let steps' =
                        let uu____16759 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____16759
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      only_strong_steps
                        (let uu___253_16765 = cfg in
                         {
                           steps = (FStar_List.append steps' cfg.steps);
                           tcenv = (uu___253_16765.tcenv);
                           delta_level = new_delta;
                           primitive_steps = (uu___253_16765.primitive_steps)
                         }) in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16797 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16818 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16878  ->
                                    fun uu____16879  ->
                                      match (uu____16878, uu____16879) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____16970 = norm_pat env3 p1 in
                                          (match uu____16970 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16818 with
                           | (pats1,env3) ->
                               ((let uu___254_17052 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___254_17052.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___255_17071 = x in
                            let uu____17072 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___255_17071.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___255_17071.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17072
                            } in
                          ((let uu___256_17086 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___256_17086.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___257_17097 = x in
                            let uu____17098 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___257_17097.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___257_17097.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17098
                            } in
                          ((let uu___258_17112 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___258_17112.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___259_17128 = x in
                            let uu____17129 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___259_17128.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___259_17128.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17129
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___260_17136 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___260_17136.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17146 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17160 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17160 with
                                  | (p,wopt,e) ->
                                      let uu____17180 = norm_pat env1 p in
                                      (match uu____17180 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17205 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17205 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17211 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17211) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17221) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17226 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17227;
                         FStar_Syntax_Syntax.fv_delta = uu____17228;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17229;
                         FStar_Syntax_Syntax.fv_delta = uu____17230;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17231);_}
                       -> true
                   | uu____17238 -> false in
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
                   let uu____17383 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17383 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17470 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____17509 ->
                                 let uu____17510 =
                                   let uu____17511 = is_cons head1 in
                                   Prims.op_Negation uu____17511 in
                                 FStar_Util.Inr uu____17510)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17536 =
                              let uu____17537 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17537.FStar_Syntax_Syntax.n in
                            (match uu____17536 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17555 ->
                                 let uu____17556 =
                                   let uu____17557 = is_cons head1 in
                                   Prims.op_Negation uu____17557 in
                                 FStar_Util.Inr uu____17556))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17626)::rest_a,(p1,uu____17629)::rest_p) ->
                       let uu____17673 = matches_pat t1 p1 in
                       (match uu____17673 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17722 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17828 = matches_pat scrutinee1 p1 in
                       (match uu____17828 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17868  ->
                                  let uu____17869 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17870 =
                                    let uu____17871 =
                                      FStar_List.map
                                        (fun uu____17881  ->
                                           match uu____17881 with
                                           | (uu____17886,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17871
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17869 uu____17870);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____17917  ->
                                       match uu____17917 with
                                       | (bv,t1) ->
                                           let uu____17940 =
                                             let uu____17947 =
                                               let uu____17950 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____17950 in
                                             let uu____17951 =
                                               let uu____17952 =
                                                 let uu____17983 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____17983, false) in
                                               Clos uu____17952 in
                                             (uu____17947, uu____17951) in
                                           uu____17940 :: env2) env1 s in
                              let uu____18092 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18092))) in
                 let uu____18093 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18093
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___193_18116  ->
                match uu___193_18116 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18120 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18126 -> d in
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
            let uu___261_18155 = config s e in
            {
              steps = (uu___261_18155.steps);
              tcenv = (uu___261_18155.tcenv);
              delta_level = (uu___261_18155.delta_level);
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
      fun t  -> let uu____18186 = config s e in norm_comp uu____18186 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18201 = config [] env in norm_universe uu____18201 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18216 = config [] env in ghost_to_pure_aux uu____18216 [] c
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
        let uu____18236 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18236 in
      let uu____18243 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18243
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___262_18245 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___262_18245.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___262_18245.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18248  ->
                    let uu____18249 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18249))
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
            ((let uu____18268 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18268);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18281 = config [AllowUnboundUniverses] env in
          norm_comp uu____18281 [] c
        with
        | e ->
            ((let uu____18294 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18294);
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
                   let uu____18334 =
                     let uu____18335 =
                       let uu____18342 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18342) in
                     FStar_Syntax_Syntax.Tm_refine uu____18335 in
                   mk uu____18334 t01.FStar_Syntax_Syntax.pos
               | uu____18347 -> t2)
          | uu____18348 -> t2 in
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
        let uu____18400 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18400 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18429 ->
                 let uu____18436 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18436 with
                  | (actuals,uu____18446,uu____18447) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18461 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18461 with
                         | (binders,args) ->
                             let uu____18478 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18478
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
      | uu____18488 ->
          let uu____18489 = FStar_Syntax_Util.head_and_args t in
          (match uu____18489 with
           | (head1,args) ->
               let uu____18526 =
                 let uu____18527 = FStar_Syntax_Subst.compress head1 in
                 uu____18527.FStar_Syntax_Syntax.n in
               (match uu____18526 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18530,thead) ->
                    let uu____18556 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18556 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18598 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___267_18606 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___267_18606.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___267_18606.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___267_18606.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___267_18606.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___267_18606.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___267_18606.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___267_18606.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___267_18606.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___267_18606.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___267_18606.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___267_18606.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___267_18606.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___267_18606.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___267_18606.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___267_18606.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___267_18606.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___267_18606.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___267_18606.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___267_18606.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___267_18606.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___267_18606.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___267_18606.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___267_18606.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___267_18606.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___267_18606.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___267_18606.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___267_18606.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___267_18606.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___267_18606.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___267_18606.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____18598 with
                            | (uu____18607,ty,uu____18609) ->
                                eta_expand_with_type env t ty))
                | uu____18610 ->
                    let uu____18611 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___268_18619 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___268_18619.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___268_18619.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___268_18619.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___268_18619.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___268_18619.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___268_18619.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___268_18619.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___268_18619.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___268_18619.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___268_18619.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___268_18619.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___268_18619.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___268_18619.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___268_18619.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___268_18619.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___268_18619.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___268_18619.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___268_18619.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___268_18619.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___268_18619.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___268_18619.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___268_18619.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___268_18619.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___268_18619.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___268_18619.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___268_18619.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___268_18619.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___268_18619.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___268_18619.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___268_18619.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____18611 with
                     | (uu____18620,ty,uu____18622) ->
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
            | (uu____18700,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18706,FStar_Util.Inl t) ->
                let uu____18712 =
                  let uu____18715 =
                    let uu____18716 =
                      let uu____18729 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18729) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18716 in
                  FStar_Syntax_Syntax.mk uu____18715 in
                uu____18712 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18733 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18733 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18760 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18815 ->
                    let uu____18816 =
                      let uu____18825 =
                        let uu____18826 = FStar_Syntax_Subst.compress t3 in
                        uu____18826.FStar_Syntax_Syntax.n in
                      (uu____18825, tc) in
                    (match uu____18816 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18851) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18888) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____18927,FStar_Util.Inl uu____18928) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____18951 -> failwith "Impossible") in
              (match uu____18760 with
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
          let uu____19060 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19060 with
          | (univ_names1,binders1,tc) ->
              let uu____19118 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19118)
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
          let uu____19157 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19157 with
          | (univ_names1,binders1,tc) ->
              let uu____19217 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19217)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19252 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19252 with
           | (univ_names1,binders1,typ1) ->
               let uu___269_19280 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___269_19280.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___269_19280.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___269_19280.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___269_19280.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___270_19301 = s in
          let uu____19302 =
            let uu____19303 =
              let uu____19312 = FStar_List.map (elim_uvars env) sigs in
              (uu____19312, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19303 in
          {
            FStar_Syntax_Syntax.sigel = uu____19302;
            FStar_Syntax_Syntax.sigrng =
              (uu___270_19301.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___270_19301.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___270_19301.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___270_19301.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19329 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19329 with
           | (univ_names1,uu____19347,typ1) ->
               let uu___271_19361 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___271_19361.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___271_19361.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___271_19361.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___271_19361.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19367 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19367 with
           | (univ_names1,uu____19385,typ1) ->
               let uu___272_19399 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___272_19399.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___272_19399.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___272_19399.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___272_19399.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19433 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19433 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19456 =
                            let uu____19457 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19457 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19456 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___273_19460 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___273_19460.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___273_19460.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___274_19461 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___274_19461.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___274_19461.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___274_19461.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___274_19461.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___275_19473 = s in
          let uu____19474 =
            let uu____19475 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19475 in
          {
            FStar_Syntax_Syntax.sigel = uu____19474;
            FStar_Syntax_Syntax.sigrng =
              (uu___275_19473.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___275_19473.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___275_19473.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___275_19473.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19479 = elim_uvars_aux_t env us [] t in
          (match uu____19479 with
           | (us1,uu____19497,t1) ->
               let uu___276_19511 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___276_19511.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___276_19511.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___276_19511.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___276_19511.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19512 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19514 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19514 with
           | (univs1,binders,signature) ->
               let uu____19542 =
                 let uu____19551 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19551 with
                 | (univs_opening,univs2) ->
                     let uu____19578 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19578) in
               (match uu____19542 with
                | (univs_opening,univs_closing) ->
                    let uu____19595 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19601 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19602 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19601, uu____19602) in
                    (match uu____19595 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19624 =
                           match uu____19624 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19642 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19642 with
                                | (us1,t1) ->
                                    let uu____19653 =
                                      let uu____19658 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19665 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19658, uu____19665) in
                                    (match uu____19653 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19678 =
                                           let uu____19683 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19692 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19683, uu____19692) in
                                         (match uu____19678 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19708 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19708 in
                                              let uu____19709 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19709 with
                                               | (uu____19730,uu____19731,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19746 =
                                                       let uu____19747 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19747 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19746 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19752 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19752 with
                           | (uu____19765,uu____19766,t1) -> t1 in
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
                             | uu____19826 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19843 =
                               let uu____19844 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19844.FStar_Syntax_Syntax.n in
                             match uu____19843 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19903 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____19932 =
                               let uu____19933 =
                                 FStar_Syntax_Subst.compress t in
                               uu____19933.FStar_Syntax_Syntax.n in
                             match uu____19932 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____19954) ->
                                 let uu____19975 = destruct_action_body body in
                                 (match uu____19975 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20020 ->
                                 let uu____20021 = destruct_action_body t in
                                 (match uu____20021 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20070 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20070 with
                           | (action_univs,t) ->
                               let uu____20079 = destruct_action_typ_templ t in
                               (match uu____20079 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___277_20120 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___277_20120.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___277_20120.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___278_20122 = ed in
                           let uu____20123 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20124 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20125 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20126 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20127 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20128 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20129 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20130 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20131 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20132 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20133 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20134 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20135 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20136 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___278_20122.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___278_20122.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20123;
                             FStar_Syntax_Syntax.bind_wp = uu____20124;
                             FStar_Syntax_Syntax.if_then_else = uu____20125;
                             FStar_Syntax_Syntax.ite_wp = uu____20126;
                             FStar_Syntax_Syntax.stronger = uu____20127;
                             FStar_Syntax_Syntax.close_wp = uu____20128;
                             FStar_Syntax_Syntax.assert_p = uu____20129;
                             FStar_Syntax_Syntax.assume_p = uu____20130;
                             FStar_Syntax_Syntax.null_wp = uu____20131;
                             FStar_Syntax_Syntax.trivial = uu____20132;
                             FStar_Syntax_Syntax.repr = uu____20133;
                             FStar_Syntax_Syntax.return_repr = uu____20134;
                             FStar_Syntax_Syntax.bind_repr = uu____20135;
                             FStar_Syntax_Syntax.actions = uu____20136
                           } in
                         let uu___279_20139 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___279_20139.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___279_20139.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___279_20139.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___279_20139.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___194_20156 =
            match uu___194_20156 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20183 = elim_uvars_aux_t env us [] t in
                (match uu____20183 with
                 | (us1,uu____20207,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___280_20226 = sub_eff in
            let uu____20227 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20230 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___280_20226.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___280_20226.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20227;
              FStar_Syntax_Syntax.lift = uu____20230
            } in
          let uu___281_20233 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___281_20233.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___281_20233.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___281_20233.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___281_20233.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20243 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20243 with
           | (univ_names1,binders1,comp1) ->
               let uu___282_20277 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___282_20277.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___282_20277.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___282_20277.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___282_20277.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20288 -> s