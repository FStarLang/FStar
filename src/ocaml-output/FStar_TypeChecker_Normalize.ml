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
      | FStar_Pervasives_Native.Some uu____1315 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1389 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1389 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___189_1396  ->
    match uu___189_1396 with
    | Arg (c,uu____1398,uu____1399) ->
        let uu____1400 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1400
    | MemoLazy uu____1401 -> "MemoLazy"
    | Abs (uu____1408,bs,uu____1410,uu____1411,uu____1412) ->
        let uu____1417 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1417
    | UnivArgs uu____1422 -> "UnivArgs"
    | Match uu____1429 -> "Match"
    | App (uu____1436,t,uu____1438,uu____1439) ->
        let uu____1440 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1440
    | Meta (m,uu____1442) -> "Meta"
    | Let uu____1443 -> "Let"
    | Steps (uu____1452,uu____1453,uu____1454) -> "Steps"
    | Debug (t,uu____1464) ->
        let uu____1465 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1465
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1473 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1473 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1489 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1489 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1502 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1502 then f () else ()
let is_empty: 'Auu____1506 . 'Auu____1506 Prims.list -> Prims.bool =
  fun uu___190_1512  ->
    match uu___190_1512 with | [] -> true | uu____1515 -> false
let lookup_bvar:
  'Auu____1522 'Auu____1523 .
    ('Auu____1523,'Auu____1522) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1522
  =
  fun env  ->
    fun x  ->
      try
        let uu____1547 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1547
      with
      | uu____1560 ->
          let uu____1561 =
            let uu____1562 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1562 in
          failwith uu____1561
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
          let uu____1599 =
            FStar_List.fold_left
              (fun uu____1625  ->
                 fun u1  ->
                   match uu____1625 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1650 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1650 with
                        | (k_u,n1) ->
                            let uu____1665 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1665
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1599 with
          | (uu____1683,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1708 =
                   let uu____1709 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1709 in
                 match uu____1708 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1727 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1736 ->
                   let uu____1737 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1737
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1743 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1752 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1761 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1768 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1768 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1785 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1785 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1793 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1801 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1801 with
                                  | (uu____1806,m) -> n1 <= m)) in
                        if uu____1793 then rest1 else us1
                    | uu____1811 -> us1)
               | uu____1816 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1820 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1820 in
        let uu____1823 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1823
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1825 = aux u in
           match uu____1825 with
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
          (fun uu____1929  ->
             let uu____1930 = FStar_Syntax_Print.tag_of_term t in
             let uu____1931 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1930
               uu____1931);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1938 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1940 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1965 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1966 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1967 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1968 ->
                  let uu____1985 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1985
                  then
                    let uu____1986 =
                      let uu____1987 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1988 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1987 uu____1988 in
                    failwith uu____1986
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1991 =
                    let uu____1992 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1992 in
                  mk uu____1991 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1999 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1999
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2001 = lookup_bvar env x in
                  (match uu____2001 with
                   | Univ uu____2004 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2008) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2120 = closures_as_binders_delayed cfg env bs in
                  (match uu____2120 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2148 =
                         let uu____2149 =
                           let uu____2166 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2166) in
                         FStar_Syntax_Syntax.Tm_abs uu____2149 in
                       mk uu____2148 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2197 = closures_as_binders_delayed cfg env bs in
                  (match uu____2197 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2239 =
                    let uu____2250 =
                      let uu____2257 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2257] in
                    closures_as_binders_delayed cfg env uu____2250 in
                  (match uu____2239 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2275 =
                         let uu____2276 =
                           let uu____2283 =
                             let uu____2284 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2284
                               FStar_Pervasives_Native.fst in
                           (uu____2283, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2276 in
                       mk uu____2275 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2375 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2375
                    | FStar_Util.Inr c ->
                        let uu____2389 = close_comp cfg env c in
                        FStar_Util.Inr uu____2389 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2405 =
                    let uu____2406 =
                      let uu____2433 = closure_as_term_delayed cfg env t11 in
                      (uu____2433, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2406 in
                  mk uu____2405 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2484 =
                    let uu____2485 =
                      let uu____2492 = closure_as_term_delayed cfg env t' in
                      let uu____2495 =
                        let uu____2496 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2496 in
                      (uu____2492, uu____2495) in
                    FStar_Syntax_Syntax.Tm_meta uu____2485 in
                  mk uu____2484 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2556 =
                    let uu____2557 =
                      let uu____2564 = closure_as_term_delayed cfg env t' in
                      let uu____2567 =
                        let uu____2568 =
                          let uu____2575 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2575) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2568 in
                      (uu____2564, uu____2567) in
                    FStar_Syntax_Syntax.Tm_meta uu____2557 in
                  mk uu____2556 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2594 =
                    let uu____2595 =
                      let uu____2602 = closure_as_term_delayed cfg env t' in
                      let uu____2605 =
                        let uu____2606 =
                          let uu____2615 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2615) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2606 in
                      (uu____2602, uu____2605) in
                    FStar_Syntax_Syntax.Tm_meta uu____2595 in
                  mk uu____2594 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2628 =
                    let uu____2629 =
                      let uu____2636 = closure_as_term_delayed cfg env t' in
                      (uu____2636, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2629 in
                  mk uu____2628 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2676  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2695 =
                    let uu____2706 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2706
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2725 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___209_2737 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___209_2737.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___209_2737.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2725)) in
                  (match uu____2695 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___210_2753 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___210_2753.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___210_2753.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2764,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2823  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2848 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2848
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2868  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2890 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2890
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___211_2902 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___211_2902.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___211_2902.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___212_2903 = lb in
                    let uu____2904 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___212_2903.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___212_2903.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2904
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2934  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3023 =
                    match uu____3023 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3078 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3099 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3159  ->
                                        fun uu____3160  ->
                                          match (uu____3159, uu____3160) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3251 =
                                                norm_pat env3 p1 in
                                              (match uu____3251 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3099 with
                               | (pats1,env3) ->
                                   ((let uu___213_3333 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___213_3333.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___214_3352 = x in
                                let uu____3353 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___214_3352.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___214_3352.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3353
                                } in
                              ((let uu___215_3367 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___215_3367.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___216_3378 = x in
                                let uu____3379 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___216_3378.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___216_3378.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3379
                                } in
                              ((let uu___217_3393 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___217_3393.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___218_3409 = x in
                                let uu____3410 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___218_3409.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___218_3409.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3410
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___219_3417 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___219_3417.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3420 = norm_pat env1 pat in
                        (match uu____3420 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3449 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3449 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3455 =
                    let uu____3456 =
                      let uu____3479 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3479) in
                    FStar_Syntax_Syntax.Tm_match uu____3456 in
                  mk uu____3455 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3565 -> closure_as_term cfg env t
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
        | uu____3591 ->
            FStar_List.map
              (fun uu____3608  ->
                 match uu____3608 with
                 | (x,imp) ->
                     let uu____3627 = closure_as_term_delayed cfg env x in
                     (uu____3627, imp)) args
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
        let uu____3641 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3690  ->
                  fun uu____3691  ->
                    match (uu____3690, uu____3691) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___220_3761 = b in
                          let uu____3762 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___220_3761.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___220_3761.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3762
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3641 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3855 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3868 = closure_as_term_delayed cfg env t in
                 let uu____3869 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3868 uu____3869
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3882 = closure_as_term_delayed cfg env t in
                 let uu____3883 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3882 uu____3883
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
                        (fun uu___191_3909  ->
                           match uu___191_3909 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3913 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3913
                           | f -> f)) in
                 let uu____3917 =
                   let uu___221_3918 = c1 in
                   let uu____3919 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3919;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___221_3918.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3917)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___192_3929  ->
            match uu___192_3929 with
            | FStar_Syntax_Syntax.DECREASES uu____3930 -> false
            | uu____3933 -> true))
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
                   (fun uu___193_3951  ->
                      match uu___193_3951 with
                      | FStar_Syntax_Syntax.DECREASES uu____3952 -> false
                      | uu____3955 -> true)) in
            let rc1 =
              let uu___222_3957 = rc in
              let uu____3958 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___222_3957.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3958;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3965 -> lopt
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
    let uu____4055 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4055 in
  let arg_as_bounded_int uu____4083 =
    match uu____4083 with
    | (a,uu____4095) ->
        let uu____4102 =
          let uu____4103 = FStar_Syntax_Subst.compress a in
          uu____4103.FStar_Syntax_Syntax.n in
        (match uu____4102 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4113;
                FStar_Syntax_Syntax.vars = uu____4114;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4116;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4117;_},uu____4118)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4157 =
               let uu____4162 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4162) in
             FStar_Pervasives_Native.Some uu____4157
         | uu____4167 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4209 = f a in FStar_Pervasives_Native.Some uu____4209
    | uu____4210 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4260 = f a0 a1 in FStar_Pervasives_Native.Some uu____4260
    | uu____4261 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4310 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4310 in
  let binary_op as_a f res args =
    let uu____4366 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4366 in
  let as_primitive_step uu____4390 =
    match uu____4390 with
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
           let uu____4438 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4438) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4466 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4466) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4487 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4487) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4515 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4515) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4543 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4543) in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4660 =
          let uu____4669 = as_a a in
          let uu____4672 = as_b b in (uu____4669, uu____4672) in
        (match uu____4660 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4687 =
               let uu____4688 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4688 in
             FStar_Pervasives_Native.Some uu____4687
         | uu____4689 -> FStar_Pervasives_Native.None)
    | uu____4698 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4712 =
        let uu____4713 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4713 in
      mk uu____4712 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4723 =
      let uu____4726 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4726 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4723 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4758 =
      let uu____4759 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4759 in
    FStar_Syntax_Embeddings.embed_int rng uu____4758 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4777 = arg_as_string a1 in
        (match uu____4777 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4783 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4783 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4796 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4796
              | uu____4797 -> FStar_Pervasives_Native.None)
         | uu____4802 -> FStar_Pervasives_Native.None)
    | uu____4805 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4815 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4815 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4839 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4850 =
          let uu____4871 = arg_as_string fn in
          let uu____4874 = arg_as_int from_line in
          let uu____4877 = arg_as_int from_col in
          let uu____4880 = arg_as_int to_line in
          let uu____4883 = arg_as_int to_col in
          (uu____4871, uu____4874, uu____4877, uu____4880, uu____4883) in
        (match uu____4850 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4914 =
                 let uu____4915 = FStar_BigInt.to_int_fs from_l in
                 let uu____4916 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4915 uu____4916 in
               let uu____4917 =
                 let uu____4918 = FStar_BigInt.to_int_fs to_l in
                 let uu____4919 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4918 uu____4919 in
               FStar_Range.mk_range fn1 uu____4914 uu____4917 in
             let uu____4920 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4920
         | uu____4925 -> FStar_Pervasives_Native.None)
    | uu____4946 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4973)::(a1,uu____4975)::(a2,uu____4977)::[] ->
        let uu____5014 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5014 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5027 -> FStar_Pervasives_Native.None)
    | uu____5028 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5055)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5064 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5088 =
      let uu____5103 =
        let uu____5118 =
          let uu____5133 =
            let uu____5148 =
              let uu____5163 =
                let uu____5178 =
                  let uu____5193 =
                    let uu____5208 =
                      let uu____5223 =
                        let uu____5238 =
                          let uu____5253 =
                            let uu____5268 =
                              let uu____5283 =
                                let uu____5298 =
                                  let uu____5313 =
                                    let uu____5328 =
                                      let uu____5343 =
                                        let uu____5358 =
                                          let uu____5373 =
                                            let uu____5388 =
                                              let uu____5401 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5401,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5408 =
                                              let uu____5423 =
                                                let uu____5436 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5436,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5447 =
                                                let uu____5462 =
                                                  let uu____5477 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5477,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5486 =
                                                  let uu____5503 =
                                                    let uu____5518 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5518,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5527 =
                                                    let uu____5544 =
                                                      let uu____5563 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5563,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5544] in
                                                  uu____5503 :: uu____5527 in
                                                uu____5462 :: uu____5486 in
                                              uu____5423 :: uu____5447 in
                                            uu____5388 :: uu____5408 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5373 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5358 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5343 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5328 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5313 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5781 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5781 y)))
                                  :: uu____5298 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5283 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5268 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5253 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5238 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5223 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5927 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5927)))
                      :: uu____5208 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5953 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5953)))
                    :: uu____5193 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5979 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5979)))
                  :: uu____5178 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____6005 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____6005)))
                :: uu____5163 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5148 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5133 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5118 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5103 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5088 in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6158 =
        let uu____6159 =
          let uu____6160 = FStar_Syntax_Syntax.as_arg c in [uu____6160] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6159 in
      uu____6158 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6210 =
                let uu____6223 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____6223, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6243  ->
                          fun uu____6244  ->
                            match (uu____6243, uu____6244) with
                            | ((int_to_t1,x),(uu____6263,y)) ->
                                let uu____6273 = FStar_BigInt.add_big_int x y in
                                int_as_bounded r int_to_t1 uu____6273))) in
              let uu____6274 =
                let uu____6289 =
                  let uu____6302 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____6302, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6322  ->
                            fun uu____6323  ->
                              match (uu____6322, uu____6323) with
                              | ((int_to_t1,x),(uu____6342,y)) ->
                                  let uu____6352 =
                                    FStar_BigInt.sub_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6352))) in
                let uu____6353 =
                  let uu____6368 =
                    let uu____6381 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____6381, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____6401  ->
                              fun uu____6402  ->
                                match (uu____6401, uu____6402) with
                                | ((int_to_t1,x),(uu____6421,y)) ->
                                    let uu____6431 =
                                      FStar_BigInt.mult_big_int x y in
                                    int_as_bounded r int_to_t1 uu____6431))) in
                  let uu____6432 =
                    let uu____6447 =
                      let uu____6460 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____6460, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____6476  ->
                                match uu____6476 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed_int r x))) in
                    [uu____6447] in
                  uu____6368 :: uu____6432 in
                uu____6289 :: uu____6353 in
              uu____6210 :: uu____6274)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6590 =
                let uu____6603 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____6603, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6623  ->
                          fun uu____6624  ->
                            match (uu____6623, uu____6624) with
                            | ((int_to_t1,x),(uu____6643,y)) ->
                                let uu____6653 = FStar_BigInt.div_big_int x y in
                                int_as_bounded r int_to_t1 uu____6653))) in
              let uu____6654 =
                let uu____6669 =
                  let uu____6682 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____6682, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6702  ->
                            fun uu____6703  ->
                              match (uu____6702, uu____6703) with
                              | ((int_to_t1,x),(uu____6722,y)) ->
                                  let uu____6732 =
                                    FStar_BigInt.mod_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6732))) in
                [uu____6669] in
              uu____6590 :: uu____6654)) in
    let div_mod_signed =
      let abs1 a =
        let uu____6788 = FStar_BigInt.le_big_int a FStar_BigInt.zero in
        if uu____6788 then FStar_BigInt.minus_big_int a else a in
      let div1 a b =
        let uu____6797 =
          ((FStar_BigInt.ge_big_int a FStar_BigInt.zero) &&
             (FStar_BigInt.lt_big_int b FStar_BigInt.zero))
            ||
            ((FStar_BigInt.lt_big_int a FStar_BigInt.zero) &&
               (FStar_BigInt.ge_big_int b FStar_BigInt.zero)) in
        if uu____6797
        then
          let uu____6798 =
            let uu____6799 = abs1 a in
            let uu____6800 = abs1 b in
            FStar_BigInt.div_big_int uu____6799 uu____6800 in
          FStar_BigInt.minus_big_int uu____6798
        else
          (let uu____6802 = abs1 a in
           let uu____6803 = abs1 b in
           FStar_BigInt.div_big_int uu____6802 uu____6803) in
      let rem1 a b =
        let uu____6811 =
          let uu____6812 = div1 a b in FStar_BigInt.mult_big_int uu____6812 b in
        FStar_BigInt.sub_big_int a uu____6811 in
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6845 =
                let uu____6858 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____6858, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6878  ->
                          fun uu____6879  ->
                            match (uu____6878, uu____6879) with
                            | ((int_to_t1,x),(uu____6898,y)) ->
                                let uu____6908 = div1 x y in
                                int_as_bounded r int_to_t1 uu____6908))) in
              let uu____6909 =
                let uu____6924 =
                  let uu____6937 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____6937, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6957  ->
                            fun uu____6958  ->
                              match (uu____6957, uu____6958) with
                              | ((int_to_t1,x),(uu____6977,y)) ->
                                  let uu____6987 = rem1 x y in
                                  int_as_bounded r int_to_t1 uu____6987))) in
                [uu____6924] in
              uu____6845 :: uu____6909)) in
    FStar_List.append add_sub_mul_v
      (FStar_List.append div_mod_unsigned div_mod_signed) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____7089)::(a1,uu____7091)::(a2,uu____7093)::[] ->
        let uu____7130 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7130 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_7136 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_7136.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_7136.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_7140 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_7140.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_7140.FStar_Syntax_Syntax.vars)
                })
         | uu____7141 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7143)::uu____7144::(a1,uu____7146)::(a2,uu____7148)::[] ->
        let uu____7197 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7197 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_7203 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_7203.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_7203.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_7207 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_7207.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_7207.FStar_Syntax_Syntax.vars)
                })
         | uu____7208 -> FStar_Pervasives_Native.None)
    | uu____7209 -> failwith "Unexpected number of arguments" in
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
      let uu____7228 =
        let uu____7229 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____7229 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____7228
    with | uu____7235 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____7239 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7239) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7299  ->
           fun subst1  ->
             match uu____7299 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____7341)) ->
                      let uu____7400 = b in
                      (match uu____7400 with
                       | (bv,uu____7408) ->
                           let uu____7409 =
                             let uu____7410 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7410 in
                           if uu____7409
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7415 = unembed_binder term1 in
                              match uu____7415 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7422 =
                                      let uu___227_7423 = bv in
                                      let uu____7424 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___227_7423.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___227_7423.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7424
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7422 in
                                  let b_for_x =
                                    let uu____7428 =
                                      let uu____7435 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7435) in
                                    FStar_Syntax_Syntax.NT uu____7428 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___194_7444  ->
                                         match uu___194_7444 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7445,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7447;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7448;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7453 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7454 -> subst1)) env []
let reduce_primops:
  'Auu____7471 'Auu____7472 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7472) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7471 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____7513 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7513
          then tm
          else
            (let uu____7515 = FStar_Syntax_Util.head_and_args tm in
             match uu____7515 with
             | (head1,args) ->
                 let uu____7552 =
                   let uu____7553 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7553.FStar_Syntax_Syntax.n in
                 (match uu____7552 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7557 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7557 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7574  ->
                                   let uu____7575 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7576 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7583 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7575 uu____7576 uu____7583);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7588  ->
                                   let uu____7589 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7589);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7592  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7594 =
                                 prim_step.interpretation psc args in
                               match uu____7594 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7600  ->
                                         let uu____7601 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7601);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7607  ->
                                         let uu____7608 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7609 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7608 uu____7609);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7610 ->
                           (log_primops cfg
                              (fun uu____7614  ->
                                 let uu____7615 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7615);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7619  ->
                            let uu____7620 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7620);
                       (match args with
                        | (a1,uu____7622)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7639 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7651  ->
                            let uu____7652 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7652);
                       (match args with
                        | (a1,uu____7654)::(a2,uu____7656)::[] ->
                            let uu____7683 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____7683 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___228_7687 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___228_7687.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___228_7687.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7690 -> tm))
                  | uu____7699 -> tm))
let reduce_equality:
  'Auu____7704 'Auu____7705 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7705) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7704 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___229_7743 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___229_7743.tcenv);
           delta_level = (uu___229_7743.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___229_7743.strong)
         }) tm
let maybe_simplify_aux:
  'Auu____7750 'Auu____7751 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7751) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7750 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7793 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7793
          then tm1
          else
            (let w t =
               let uu___230_7805 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___230_7805.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___230_7805.FStar_Syntax_Syntax.vars)
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
               | uu____7822 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7827 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7827
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7848 =
                 match uu____7848 with
                 | (t1,q) ->
                     let uu____7861 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7861 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7889 -> (t1, q)) in
               let uu____7898 = FStar_Syntax_Util.head_and_args t in
               match uu____7898 with
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
                         FStar_Syntax_Syntax.pos = uu____7995;
                         FStar_Syntax_Syntax.vars = uu____7996;_},uu____7997);
                    FStar_Syntax_Syntax.pos = uu____7998;
                    FStar_Syntax_Syntax.vars = uu____7999;_},args)
                 ->
                 let uu____8025 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8025
                 then
                   let uu____8026 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8026 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8081)::
                        (uu____8082,(arg,uu____8084))::[] ->
                        maybe_auto_squash arg
                    | (uu____8149,(arg,uu____8151))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8152)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8217)::uu____8218::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8281::(FStar_Pervasives_Native.Some (false
                                   ),uu____8282)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8345 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____8361 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8361
                    then
                      let uu____8362 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8362 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8417)::uu____8418::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8481::(FStar_Pervasives_Native.Some (true
                                     ),uu____8482)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8545)::
                          (uu____8546,(arg,uu____8548))::[] ->
                          maybe_auto_squash arg
                      | (uu____8613,(arg,uu____8615))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8616)::[]
                          -> maybe_auto_squash arg
                      | uu____8681 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8697 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8697
                       then
                         let uu____8698 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8698 with
                         | uu____8753::(FStar_Pervasives_Native.Some (true
                                        ),uu____8754)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8817)::uu____8818::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8881)::
                             (uu____8882,(arg,uu____8884))::[] ->
                             maybe_auto_squash arg
                         | (uu____8949,(p,uu____8951))::(uu____8952,(q,uu____8954))::[]
                             ->
                             let uu____9019 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9019
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9021 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9037 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9037
                          then
                            let uu____9038 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9038 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9093)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9132)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9171 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____9187 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9187
                             then
                               match args with
                               | (t,uu____9189)::[] ->
                                   let uu____9206 =
                                     let uu____9207 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9207.FStar_Syntax_Syntax.n in
                                   (match uu____9206 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9210::[],body,uu____9212) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9239 -> tm1)
                                    | uu____9242 -> tm1)
                               | (uu____9243,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9244))::
                                   (t,uu____9246)::[] ->
                                   let uu____9285 =
                                     let uu____9286 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9286.FStar_Syntax_Syntax.n in
                                   (match uu____9285 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9289::[],body,uu____9291) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9318 -> tm1)
                                    | uu____9321 -> tm1)
                               | uu____9322 -> tm1
                             else
                               (let uu____9332 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9332
                                then
                                  match args with
                                  | (t,uu____9334)::[] ->
                                      let uu____9351 =
                                        let uu____9352 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9352.FStar_Syntax_Syntax.n in
                                      (match uu____9351 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9355::[],body,uu____9357)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9384 -> tm1)
                                       | uu____9387 -> tm1)
                                  | (uu____9388,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9389))::(t,uu____9391)::[] ->
                                      let uu____9430 =
                                        let uu____9431 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9431.FStar_Syntax_Syntax.n in
                                      (match uu____9430 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9434::[],body,uu____9436)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9463 -> tm1)
                                       | uu____9466 -> tm1)
                                  | uu____9467 -> tm1
                                else
                                  (let uu____9477 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9477
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9478;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9479;_},uu____9480)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9497;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9498;_},uu____9499)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9516 -> tm1
                                   else
                                     (let uu____9526 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____9526 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9546 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9556;
                    FStar_Syntax_Syntax.vars = uu____9557;_},args)
                 ->
                 let uu____9579 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9579
                 then
                   let uu____9580 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9580 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9635)::
                        (uu____9636,(arg,uu____9638))::[] ->
                        maybe_auto_squash arg
                    | (uu____9703,(arg,uu____9705))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9706)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9771)::uu____9772::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9835::(FStar_Pervasives_Native.Some (false
                                   ),uu____9836)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9899 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9915 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9915
                    then
                      let uu____9916 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9916 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9971)::uu____9972::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10035::(FStar_Pervasives_Native.Some (true
                                      ),uu____10036)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____10099)::
                          (uu____10100,(arg,uu____10102))::[] ->
                          maybe_auto_squash arg
                      | (uu____10167,(arg,uu____10169))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____10170)::[]
                          -> maybe_auto_squash arg
                      | uu____10235 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____10251 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____10251
                       then
                         let uu____10252 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____10252 with
                         | uu____10307::(FStar_Pervasives_Native.Some (true
                                         ),uu____10308)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10371)::uu____10372::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10435)::
                             (uu____10436,(arg,uu____10438))::[] ->
                             maybe_auto_squash arg
                         | (uu____10503,(p,uu____10505))::(uu____10506,
                                                           (q,uu____10508))::[]
                             ->
                             let uu____10573 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10573
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10575 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10591 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10591
                          then
                            let uu____10592 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10592 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10647)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10686)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10725 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10741 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10741
                             then
                               match args with
                               | (t,uu____10743)::[] ->
                                   let uu____10760 =
                                     let uu____10761 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10761.FStar_Syntax_Syntax.n in
                                   (match uu____10760 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10764::[],body,uu____10766) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10793 -> tm1)
                                    | uu____10796 -> tm1)
                               | (uu____10797,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10798))::
                                   (t,uu____10800)::[] ->
                                   let uu____10839 =
                                     let uu____10840 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10840.FStar_Syntax_Syntax.n in
                                   (match uu____10839 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10843::[],body,uu____10845) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10872 -> tm1)
                                    | uu____10875 -> tm1)
                               | uu____10876 -> tm1
                             else
                               (let uu____10886 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10886
                                then
                                  match args with
                                  | (t,uu____10888)::[] ->
                                      let uu____10905 =
                                        let uu____10906 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10906.FStar_Syntax_Syntax.n in
                                      (match uu____10905 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10909::[],body,uu____10911)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10938 -> tm1)
                                       | uu____10941 -> tm1)
                                  | (uu____10942,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10943))::(t,uu____10945)::[] ->
                                      let uu____10984 =
                                        let uu____10985 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10985.FStar_Syntax_Syntax.n in
                                      (match uu____10984 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10988::[],body,uu____10990)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11017 -> tm1)
                                       | uu____11020 -> tm1)
                                  | uu____11021 -> tm1
                                else
                                  (let uu____11031 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____11031
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11032;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11033;_},uu____11034)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11051;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11052;_},uu____11053)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11070 -> tm1
                                   else
                                     (let uu____11080 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____11080 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____11100 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____11109 -> tm1)
let maybe_simplify:
  'Auu____11116 'Auu____11117 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11117) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11116 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____11160 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____11160
           then
             let uu____11161 = FStar_Syntax_Print.term_to_string tm in
             let uu____11162 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____11161 uu____11162
           else ());
          tm'
let is_norm_request:
  'Auu____11168 .
    FStar_Syntax_Syntax.term -> 'Auu____11168 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11181 =
        let uu____11188 =
          let uu____11189 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11189.FStar_Syntax_Syntax.n in
        (uu____11188, args) in
      match uu____11181 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11195::uu____11196::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11200::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11205::uu____11206::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11209 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___195_11220  ->
    match uu___195_11220 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11226 =
          let uu____11229 =
            let uu____11230 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____11230 in
          [uu____11229] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____11226
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____11245 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____11245) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11283 =
          let uu____11286 =
            let uu____11291 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____11291 s in
          FStar_All.pipe_right uu____11286 FStar_Util.must in
        FStar_All.pipe_right uu____11283 tr_norm_steps in
      match args with
      | uu____11316::(tm,uu____11318)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11341)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11356)::uu____11357::(tm,uu____11359)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11399 =
              let uu____11402 = full_norm steps in parse_steps uu____11402 in
            Beta :: uu____11399 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11411 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___196_11428  ->
    match uu___196_11428 with
    | (App
        (uu____11431,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11432;
                       FStar_Syntax_Syntax.vars = uu____11433;_},uu____11434,uu____11435))::uu____11436
        -> true
    | uu____11443 -> false
let firstn:
  'Auu____11449 .
    Prims.int ->
      'Auu____11449 Prims.list ->
        ('Auu____11449 Prims.list,'Auu____11449 Prims.list)
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
          (uu____11485,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11486;
                         FStar_Syntax_Syntax.vars = uu____11487;_},uu____11488,uu____11489))::uu____11490
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11497 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11613  ->
               let uu____11614 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11615 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11616 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11623 =
                 let uu____11624 =
                   let uu____11627 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11627 in
                 stack_to_string uu____11624 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11614 uu____11615 uu____11616 uu____11623);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11650 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11675 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11692 =
                 let uu____11693 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11694 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11693 uu____11694 in
               failwith uu____11692
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11695 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11712 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11713 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11714;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11715;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11718;
                 FStar_Syntax_Syntax.fv_delta = uu____11719;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11720;
                 FStar_Syntax_Syntax.fv_delta = uu____11721;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11722);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11730 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11730 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11736  ->
                     let uu____11737 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11738 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11737 uu____11738);
                if b
                then
                  (let uu____11739 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11739 t1 fv)
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
                 let uu___231_11778 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___231_11778.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___231_11778.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11811 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11811) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___232_11819 = cfg in
                 let uu____11820 =
                   FStar_List.filter
                     (fun uu___197_11823  ->
                        match uu___197_11823 with
                        | UnfoldOnly uu____11824 -> false
                        | NoDeltaSteps  -> false
                        | uu____11827 -> true) cfg.steps in
                 {
                   steps = uu____11820;
                   tcenv = (uu___232_11819.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___232_11819.primitive_steps);
                   strong = (uu___232_11819.strong)
                 } in
               let uu____11828 = get_norm_request (norm cfg' env []) args in
               (match uu____11828 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11844 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___198_11849  ->
                                match uu___198_11849 with
                                | UnfoldUntil uu____11850 -> true
                                | UnfoldOnly uu____11851 -> true
                                | uu____11854 -> false)) in
                      if uu____11844
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___233_11859 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___233_11859.tcenv);
                        delta_level;
                        primitive_steps = (uu___233_11859.primitive_steps);
                        strong = (uu___233_11859.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____11870 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11870
                      then
                        let uu____11873 =
                          let uu____11874 =
                            let uu____11879 = FStar_Util.now () in
                            (t1, uu____11879) in
                          Debug uu____11874 in
                        uu____11873 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11881;
                  FStar_Syntax_Syntax.vars = uu____11882;_},a1::a2::rest)
               ->
               let uu____11930 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11930 with
                | (hd1,uu____11946) ->
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
                  FStar_Syntax_Syntax.pos = uu____12011;
                  FStar_Syntax_Syntax.vars = uu____12012;_},a1::a2::rest)
               ->
               let uu____12060 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____12060 with
                | (hd1,uu____12076) ->
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
                  FStar_Syntax_Syntax.pos = uu____12141;
                  FStar_Syntax_Syntax.vars = uu____12142;_},a1::a2::a3::rest)
               ->
               let uu____12203 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____12203 with
                | (hd1,uu____12219) ->
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
                    (FStar_Const.Const_reflect uu____12290);
                  FStar_Syntax_Syntax.pos = uu____12291;
                  FStar_Syntax_Syntax.vars = uu____12292;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____12324 = FStar_List.tl stack in
               norm cfg env uu____12324 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____12327;
                  FStar_Syntax_Syntax.vars = uu____12328;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____12360 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____12360 with
                | (reify_head,uu____12376) ->
                    let a1 =
                      let uu____12398 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____12398 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____12401);
                            FStar_Syntax_Syntax.pos = uu____12402;
                            FStar_Syntax_Syntax.vars = uu____12403;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____12437 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____12447 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____12447
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____12454 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____12454
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12457 =
                      let uu____12464 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____12464, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____12457 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___199_12477  ->
                         match uu___199_12477 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____12480 =
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
                 if uu____12480
                 then false
                 else
                   (let uu____12482 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___200_12489  ->
                              match uu___200_12489 with
                              | UnfoldOnly uu____12490 -> true
                              | uu____12493 -> false)) in
                    match uu____12482 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____12497 -> should_delta) in
               (log cfg
                  (fun uu____12505  ->
                     let uu____12506 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____12507 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____12508 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____12506 uu____12507 uu____12508);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12511 = lookup_bvar env x in
               (match uu____12511 with
                | Univ uu____12514 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____12563 = FStar_ST.op_Bang r in
                      (match uu____12563 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12702  ->
                                 let uu____12703 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12704 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12703
                                   uu____12704);
                            (let uu____12705 =
                               let uu____12706 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12706.FStar_Syntax_Syntax.n in
                             match uu____12705 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12709 ->
                                 norm cfg env2 stack t'
                             | uu____12726 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12784)::uu____12785 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12794)::uu____12795 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12805,uu____12806))::stack_rest ->
                    (match c with
                     | Univ uu____12810 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12819 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12840  ->
                                    let uu____12841 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12841);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12881  ->
                                    let uu____12882 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12882);
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
                      (let uu___234_12932 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___234_12932.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___234_12932.strong)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12965  ->
                          let uu____12966 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12966);
                     norm cfg env stack1 t1)
                | (Debug uu____12967)::uu____12968 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12975 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12975
                    else
                      (let uu____12977 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12977 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13019  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13047 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13047
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13057 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13057)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13062 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13062.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13062.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13063 -> lopt in
                           (log cfg
                              (fun uu____13069  ->
                                 let uu____13070 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13070);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13083 = cfg in
                               {
                                 steps = (uu___236_13083.steps);
                                 tcenv = (uu___236_13083.tcenv);
                                 delta_level = (uu___236_13083.delta_level);
                                 primitive_steps =
                                   (uu___236_13083.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13094)::uu____13095 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13102 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13102
                    else
                      (let uu____13104 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13104 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13146  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13174 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13174
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13184 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13184)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13189 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13189.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13189.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13190 -> lopt in
                           (log cfg
                              (fun uu____13196  ->
                                 let uu____13197 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13197);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13210 = cfg in
                               {
                                 steps = (uu___236_13210.steps);
                                 tcenv = (uu___236_13210.tcenv);
                                 delta_level = (uu___236_13210.delta_level);
                                 primitive_steps =
                                   (uu___236_13210.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13221)::uu____13222 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13233 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13233
                    else
                      (let uu____13235 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13235 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13277  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13305 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13305
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13315 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13315)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13320 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13320.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13320.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13321 -> lopt in
                           (log cfg
                              (fun uu____13327  ->
                                 let uu____13328 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13328);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13341 = cfg in
                               {
                                 steps = (uu___236_13341.steps);
                                 tcenv = (uu___236_13341.tcenv);
                                 delta_level = (uu___236_13341.delta_level);
                                 primitive_steps =
                                   (uu___236_13341.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13352)::uu____13353 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13364 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13364
                    else
                      (let uu____13366 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13366 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13408  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13436 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13436
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13446 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13446)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13451 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13451.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13451.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13452 -> lopt in
                           (log cfg
                              (fun uu____13458  ->
                                 let uu____13459 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13459);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13472 = cfg in
                               {
                                 steps = (uu___236_13472.steps);
                                 tcenv = (uu___236_13472.tcenv);
                                 delta_level = (uu___236_13472.delta_level);
                                 primitive_steps =
                                   (uu___236_13472.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13483)::uu____13484 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13499 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13499
                    else
                      (let uu____13501 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13501 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13543  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13571 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13571
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13581 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13581)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13586 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13586.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13586.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13587 -> lopt in
                           (log cfg
                              (fun uu____13593  ->
                                 let uu____13594 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13594);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13607 = cfg in
                               {
                                 steps = (uu___236_13607.steps);
                                 tcenv = (uu___236_13607.tcenv);
                                 delta_level = (uu___236_13607.delta_level);
                                 primitive_steps =
                                   (uu___236_13607.primitive_steps);
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
                      let uu____13618 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13618
                    else
                      (let uu____13620 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13620 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13662  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13690 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13690
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13700 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13700)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13705 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13705.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13705.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13706 -> lopt in
                           (log cfg
                              (fun uu____13712  ->
                                 let uu____13713 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13713);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13726 = cfg in
                               {
                                 steps = (uu___236_13726.steps);
                                 tcenv = (uu___236_13726.tcenv);
                                 delta_level = (uu___236_13726.delta_level);
                                 primitive_steps =
                                   (uu___236_13726.primitive_steps);
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
                      (fun uu____13775  ->
                         fun stack1  ->
                           match uu____13775 with
                           | (a,aq) ->
                               let uu____13787 =
                                 let uu____13788 =
                                   let uu____13795 =
                                     let uu____13796 =
                                       let uu____13827 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13827, false) in
                                     Clos uu____13796 in
                                   (uu____13795, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13788 in
                               uu____13787 :: stack1) args) in
               (log cfg
                  (fun uu____13903  ->
                     let uu____13904 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13904);
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
                             ((let uu___237_13940 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___237_13940.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___237_13940.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13941 ->
                      let uu____13946 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13946)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13949 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13949 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13980 =
                          let uu____13981 =
                            let uu____13988 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___238_13990 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___238_13990.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___238_13990.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13988) in
                          FStar_Syntax_Syntax.Tm_refine uu____13981 in
                        mk uu____13980 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____14009 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____14009
               else
                 (let uu____14011 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____14011 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14019 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14043  -> dummy :: env1) env) in
                        norm_comp cfg uu____14019 c1 in
                      let t2 =
                        let uu____14065 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____14065 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14124)::uu____14125 ->
                    (log cfg
                       (fun uu____14136  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14137)::uu____14138 ->
                    (log cfg
                       (fun uu____14149  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14150,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14151;
                                   FStar_Syntax_Syntax.vars = uu____14152;_},uu____14153,uu____14154))::uu____14155
                    ->
                    (log cfg
                       (fun uu____14164  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14165)::uu____14166 ->
                    (log cfg
                       (fun uu____14177  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14178 ->
                    (log cfg
                       (fun uu____14181  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____14185  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14202 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____14202
                         | FStar_Util.Inr c ->
                             let uu____14210 = norm_comp cfg env c in
                             FStar_Util.Inr uu____14210 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Steps (s,ps,dl))::stack1 ->
                           let t2 =
                             let uu____14233 =
                               let uu____14234 =
                                 let uu____14261 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____14261, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14234 in
                             mk uu____14233 t1.FStar_Syntax_Syntax.pos in
                           norm
                             (let uu___239_14282 = cfg in
                              {
                                steps = s;
                                tcenv = (uu___239_14282.tcenv);
                                delta_level = dl;
                                primitive_steps = ps;
                                strong = (uu___239_14282.strong)
                              }) env stack1 t2
                       | uu____14283 ->
                           let uu____14284 =
                             let uu____14285 =
                               let uu____14286 =
                                 let uu____14313 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____14313, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14286 in
                             mk uu____14285 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____14284))))
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
                         let uu____14423 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____14423 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___240_14443 = cfg in
                               let uu____14444 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___240_14443.steps);
                                 tcenv = uu____14444;
                                 delta_level = (uu___240_14443.delta_level);
                                 primitive_steps =
                                   (uu___240_14443.primitive_steps);
                                 strong = (uu___240_14443.strong)
                               } in
                             let norm1 t2 =
                               let uu____14449 =
                                 let uu____14450 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____14450 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14449 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___241_14453 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___241_14453.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___241_14453.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____14454 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____14454
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14465,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14466;
                               FStar_Syntax_Syntax.lbunivs = uu____14467;
                               FStar_Syntax_Syntax.lbtyp = uu____14468;
                               FStar_Syntax_Syntax.lbeff = uu____14469;
                               FStar_Syntax_Syntax.lbdef = uu____14470;_}::uu____14471),uu____14472)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____14508 =
                 (let uu____14511 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____14511) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____14513 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____14513))) in
               if uu____14508
               then
                 let binder =
                   let uu____14515 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____14515 in
                 let env1 =
                   let uu____14525 =
                     let uu____14532 =
                       let uu____14533 =
                         let uu____14564 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14564,
                           false) in
                       Clos uu____14533 in
                     ((FStar_Pervasives_Native.Some binder), uu____14532) in
                   uu____14525 :: env in
                 (log cfg
                    (fun uu____14649  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____14651 =
                    let uu____14656 =
                      let uu____14657 =
                        let uu____14658 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14658
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14657] in
                    FStar_Syntax_Subst.open_term uu____14656 body in
                  match uu____14651 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____14667  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____14675 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____14675 in
                          FStar_Util.Inl
                            (let uu___242_14685 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___242_14685.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___242_14685.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____14688  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___243_14690 = lb in
                           let uu____14691 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___243_14690.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___243_14690.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____14691
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____14726  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___244_14746 = cfg in
                           {
                             steps = (uu___244_14746.steps);
                             tcenv = (uu___244_14746.tcenv);
                             delta_level = (uu___244_14746.delta_level);
                             primitive_steps =
                               (uu___244_14746.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____14749  ->
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
               let uu____14766 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14766 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14802 =
                               let uu___245_14803 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___245_14803.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___245_14803.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14802 in
                           let uu____14804 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14804 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14830 =
                                   FStar_List.map (fun uu____14846  -> dummy)
                                     lbs1 in
                                 let uu____14847 =
                                   let uu____14856 =
                                     FStar_List.map
                                       (fun uu____14876  -> dummy) xs1 in
                                   FStar_List.append uu____14856 env in
                                 FStar_List.append uu____14830 uu____14847 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14900 =
                                       let uu___246_14901 = rc in
                                       let uu____14902 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___246_14901.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14902;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___246_14901.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14900
                                 | uu____14909 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___247_14913 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___247_14913.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___247_14913.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14923 =
                        FStar_List.map (fun uu____14939  -> dummy) lbs2 in
                      FStar_List.append uu____14923 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14947 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14947 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___248_14963 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___248_14963.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___248_14963.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14990 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14990
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15009 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15085  ->
                        match uu____15085 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___249_15206 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___249_15206.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___249_15206.FStar_Syntax_Syntax.sort)
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
               (match uu____15009 with
                | (rec_env,memos,uu____15403) ->
                    let uu____15456 =
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
                             let uu____15993 =
                               let uu____16000 =
                                 let uu____16001 =
                                   let uu____16032 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16032, false) in
                                 Clos uu____16001 in
                               (FStar_Pervasives_Native.None, uu____16000) in
                             uu____15993 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____16137 =
                      let uu____16138 = should_reify cfg stack in
                      Prims.op_Negation uu____16138 in
                    if uu____16137
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____16148 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____16148
                        then
                          let uu___250_16149 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___250_16149.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___250_16149.primitive_steps);
                            strong = (uu___250_16149.strong)
                          }
                        else
                          (let uu___251_16151 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___251_16151.tcenv);
                             delta_level = (uu___251_16151.delta_level);
                             primitive_steps =
                               (uu___251_16151.primitive_steps);
                             strong = (uu___251_16151.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____16153 =
                         let uu____16154 = FStar_Syntax_Subst.compress head1 in
                         uu____16154.FStar_Syntax_Syntax.n in
                       match uu____16153 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____16172 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____16172 with
                            | (uu____16173,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____16179 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____16187 =
                                         let uu____16188 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____16188.FStar_Syntax_Syntax.n in
                                       match uu____16187 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____16194,uu____16195))
                                           ->
                                           let uu____16204 =
                                             let uu____16205 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____16205.FStar_Syntax_Syntax.n in
                                           (match uu____16204 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____16211,msrc,uu____16213))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____16222 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____16222
                                            | uu____16223 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____16224 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____16225 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____16225 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___252_16230 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___252_16230.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___252_16230.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___252_16230.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____16231 =
                                            FStar_List.tl stack in
                                          let uu____16232 =
                                            let uu____16233 =
                                              let uu____16236 =
                                                let uu____16237 =
                                                  let uu____16250 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____16250) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____16237 in
                                              FStar_Syntax_Syntax.mk
                                                uu____16236 in
                                            uu____16233
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____16231
                                            uu____16232
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____16266 =
                                            let uu____16267 = is_return body in
                                            match uu____16267 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____16271;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____16272;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____16277 -> false in
                                          if uu____16266
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
                                               let uu____16301 =
                                                 let uu____16304 =
                                                   let uu____16305 =
                                                     let uu____16322 =
                                                       let uu____16325 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____16325] in
                                                     (uu____16322, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____16305 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____16304 in
                                               uu____16301
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____16341 =
                                                 let uu____16342 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____16342.FStar_Syntax_Syntax.n in
                                               match uu____16341 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____16348::uu____16349::[])
                                                   ->
                                                   let uu____16356 =
                                                     let uu____16359 =
                                                       let uu____16360 =
                                                         let uu____16367 =
                                                           let uu____16370 =
                                                             let uu____16371
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____16371 in
                                                           let uu____16372 =
                                                             let uu____16375
                                                               =
                                                               let uu____16376
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____16376 in
                                                             [uu____16375] in
                                                           uu____16370 ::
                                                             uu____16372 in
                                                         (bind1, uu____16367) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____16360 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____16359 in
                                                   uu____16356
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____16384 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____16390 =
                                                 let uu____16393 =
                                                   let uu____16394 =
                                                     let uu____16409 =
                                                       let uu____16412 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____16413 =
                                                         let uu____16416 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____16417 =
                                                           let uu____16420 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____16421 =
                                                             let uu____16424
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____16425
                                                               =
                                                               let uu____16428
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____16429
                                                                 =
                                                                 let uu____16432
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____16432] in
                                                               uu____16428 ::
                                                                 uu____16429 in
                                                             uu____16424 ::
                                                               uu____16425 in
                                                           uu____16420 ::
                                                             uu____16421 in
                                                         uu____16416 ::
                                                           uu____16417 in
                                                       uu____16412 ::
                                                         uu____16413 in
                                                     (bind_inst, uu____16409) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____16394 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____16393 in
                                               uu____16390
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____16440 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____16440 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____16464 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____16464 with
                            | (uu____16465,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____16500 =
                                        let uu____16501 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____16501.FStar_Syntax_Syntax.n in
                                      match uu____16500 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____16507) -> t4
                                      | uu____16512 -> head2 in
                                    let uu____16513 =
                                      let uu____16514 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____16514.FStar_Syntax_Syntax.n in
                                    match uu____16513 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____16520 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____16521 = maybe_extract_fv head2 in
                                  match uu____16521 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____16531 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____16531
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____16536 =
                                          maybe_extract_fv head3 in
                                        match uu____16536 with
                                        | FStar_Pervasives_Native.Some
                                            uu____16541 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____16542 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____16547 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____16562 =
                                    match uu____16562 with
                                    | (e,q) ->
                                        let uu____16569 =
                                          let uu____16570 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____16570.FStar_Syntax_Syntax.n in
                                        (match uu____16569 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____16585 -> false) in
                                  let uu____16586 =
                                    let uu____16587 =
                                      let uu____16594 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____16594 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____16587 in
                                  if uu____16586
                                  then
                                    let uu____16599 =
                                      let uu____16600 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____16600 in
                                    failwith uu____16599
                                  else ());
                                 (let uu____16602 =
                                    maybe_unfold_action head_app in
                                  match uu____16602 with
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
                                      let uu____16641 = FStar_List.tl stack in
                                      norm cfg env uu____16641 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16655 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16655 in
                           let uu____16656 = FStar_List.tl stack in
                           norm cfg env uu____16656 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16777  ->
                                     match uu____16777 with
                                     | (pat,wopt,tm) ->
                                         let uu____16825 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16825))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16857 = FStar_List.tl stack in
                           norm cfg env uu____16857 tm
                       | uu____16858 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16866 = should_reify cfg stack in
                    if uu____16866
                    then
                      let uu____16867 = FStar_List.tl stack in
                      let uu____16868 =
                        let uu____16869 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16869 in
                      norm cfg env uu____16867 uu____16868
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16872 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16872
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___253_16881 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___253_16881.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___253_16881.primitive_steps);
                             strong = (uu___253_16881.strong)
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
                | uu____16883 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____16885::uu____16886 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16891) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16892 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____16923 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16937 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16937
                             | uu____16948 -> m in
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
              let uu____16960 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16960 in
            let uu____16961 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16961 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16974  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16985  ->
                      let uu____16986 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16987 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16986
                        uu____16987);
                 (let t1 =
                    let uu____16989 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16989
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
                    | (UnivArgs (us',uu____16999))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____17054 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____17057 ->
                        let uu____17060 =
                          let uu____17061 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____17061 in
                        failwith uu____17060
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
              let uu____17071 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____17071 with
              | (uu____17072,return_repr) ->
                  let return_inst =
                    let uu____17081 =
                      let uu____17082 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____17082.FStar_Syntax_Syntax.n in
                    match uu____17081 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____17088::[]) ->
                        let uu____17095 =
                          let uu____17098 =
                            let uu____17099 =
                              let uu____17106 =
                                let uu____17109 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____17109] in
                              (return_tm, uu____17106) in
                            FStar_Syntax_Syntax.Tm_uinst uu____17099 in
                          FStar_Syntax_Syntax.mk uu____17098 in
                        uu____17095 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____17117 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____17120 =
                    let uu____17123 =
                      let uu____17124 =
                        let uu____17139 =
                          let uu____17142 = FStar_Syntax_Syntax.as_arg t in
                          let uu____17143 =
                            let uu____17146 = FStar_Syntax_Syntax.as_arg e in
                            [uu____17146] in
                          uu____17142 :: uu____17143 in
                        (return_inst, uu____17139) in
                      FStar_Syntax_Syntax.Tm_app uu____17124 in
                    FStar_Syntax_Syntax.mk uu____17123 in
                  uu____17120 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____17155 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____17155 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17158 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____17158
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17159;
                     FStar_TypeChecker_Env.mtarget = uu____17160;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17161;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17176;
                     FStar_TypeChecker_Env.mtarget = uu____17177;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17178;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17202 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____17203 = FStar_Syntax_Util.mk_reify e in
                   lift uu____17202 t FStar_Syntax_Syntax.tun uu____17203)
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
                (fun uu____17259  ->
                   match uu____17259 with
                   | (a,imp) ->
                       let uu____17270 = norm cfg env [] a in
                       (uu____17270, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___254_17287 = comp1 in
            let uu____17290 =
              let uu____17291 =
                let uu____17300 = norm cfg env [] t in
                let uu____17301 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____17300, uu____17301) in
              FStar_Syntax_Syntax.Total uu____17291 in
            {
              FStar_Syntax_Syntax.n = uu____17290;
              FStar_Syntax_Syntax.pos =
                (uu___254_17287.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___254_17287.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___255_17316 = comp1 in
            let uu____17319 =
              let uu____17320 =
                let uu____17329 = norm cfg env [] t in
                let uu____17330 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____17329, uu____17330) in
              FStar_Syntax_Syntax.GTotal uu____17320 in
            {
              FStar_Syntax_Syntax.n = uu____17319;
              FStar_Syntax_Syntax.pos =
                (uu___255_17316.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___255_17316.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____17382  ->
                      match uu____17382 with
                      | (a,i) ->
                          let uu____17393 = norm cfg env [] a in
                          (uu____17393, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___201_17404  ->
                      match uu___201_17404 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17408 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____17408
                      | f -> f)) in
            let uu___256_17412 = comp1 in
            let uu____17415 =
              let uu____17416 =
                let uu___257_17417 = ct in
                let uu____17418 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____17419 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____17422 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____17418;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___257_17417.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____17419;
                  FStar_Syntax_Syntax.effect_args = uu____17422;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____17416 in
            {
              FStar_Syntax_Syntax.n = uu____17415;
              FStar_Syntax_Syntax.pos =
                (uu___256_17412.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___256_17412.FStar_Syntax_Syntax.vars)
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
            (let uu___258_17440 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___258_17440.tcenv);
               delta_level = (uu___258_17440.delta_level);
               primitive_steps = (uu___258_17440.primitive_steps);
               strong = (uu___258_17440.strong)
             }) env [] t in
        let non_info t =
          let uu____17445 = norm1 t in
          FStar_Syntax_Util.non_informative uu____17445 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____17448 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___259_17467 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___259_17467.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___259_17467.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____17474 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____17474
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
                    let uu___260_17485 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___260_17485.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___260_17485.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___260_17485.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___261_17487 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___261_17487.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___261_17487.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___261_17487.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___261_17487.FStar_Syntax_Syntax.flags)
                    } in
              let uu___262_17488 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___262_17488.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___262_17488.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____17490 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____17493  ->
        match uu____17493 with
        | (x,imp) ->
            let uu____17496 =
              let uu___263_17497 = x in
              let uu____17498 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___263_17497.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___263_17497.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17498
              } in
            (uu____17496, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17504 =
          FStar_List.fold_left
            (fun uu____17522  ->
               fun b  ->
                 match uu____17522 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____17504 with | (nbs,uu____17562) -> FStar_List.rev nbs
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
            let uu____17578 =
              let uu___264_17579 = rc in
              let uu____17580 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___264_17579.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17580;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___264_17579.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17578
        | uu____17587 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17600  ->
               let uu____17601 = FStar_Syntax_Print.tag_of_term t in
               let uu____17602 = FStar_Syntax_Print.term_to_string t in
               let uu____17603 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17610 =
                 let uu____17611 =
                   let uu____17614 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17614 in
                 stack_to_string uu____17611 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____17601 uu____17602 uu____17603 uu____17610);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____17643 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____17643
                 then
                   let time_now = FStar_Util.now () in
                   let uu____17645 =
                     let uu____17646 =
                       let uu____17647 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17647 in
                     FStar_Util.string_of_int uu____17646 in
                   let uu____17652 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17653 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17645 uu____17652 uu____17653
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___265_17671 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___265_17671.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___265_17671.strong)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____17712  ->
                     let uu____17713 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17713);
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
               let uu____17749 =
                 let uu___266_17750 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___266_17750.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___266_17750.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____17749
           | (Arg (Univ uu____17751,uu____17752,uu____17753))::uu____17754 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17757,uu____17758))::uu____17759 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____17775),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17828  ->
                     let uu____17829 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17829);
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
                  (let uu____17839 = FStar_ST.op_Bang m in
                   match uu____17839 with
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
                   | FStar_Pervasives_Native.Some (uu____17985,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____18028 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____18028
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18040  ->
                     let uu____18041 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18041);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____18046 =
                   log cfg
                     (fun uu____18051  ->
                        let uu____18052 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____18053 =
                          let uu____18054 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18071  ->
                                    match uu____18071 with
                                    | (p,uu____18081,uu____18082) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____18054
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18052 uu____18053);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___202_18099  ->
                                match uu___202_18099 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18100 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___267_18104 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___267_18104.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___267_18104.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18136 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18157 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18217  ->
                                    fun uu____18218  ->
                                      match (uu____18217, uu____18218) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18309 = norm_pat env3 p1 in
                                          (match uu____18309 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____18157 with
                           | (pats1,env3) ->
                               ((let uu___268_18391 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___268_18391.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___269_18410 = x in
                            let uu____18411 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___269_18410.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___269_18410.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18411
                            } in
                          ((let uu___270_18425 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___270_18425.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___271_18436 = x in
                            let uu____18437 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___271_18436.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___271_18436.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18437
                            } in
                          ((let uu___272_18451 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___272_18451.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___273_18467 = x in
                            let uu____18468 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___273_18467.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___273_18467.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18468
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___274_18475 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___274_18475.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18485 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18499 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____18499 with
                                  | (p,wopt,e) ->
                                      let uu____18519 = norm_pat env1 p in
                                      (match uu____18519 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18544 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18544 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____18550 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____18550) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18560) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18565 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18566;
                         FStar_Syntax_Syntax.fv_delta = uu____18567;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18568;
                         FStar_Syntax_Syntax.fv_delta = uu____18569;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18570);_}
                       -> true
                   | uu____18577 -> false in
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
                   let uu____18722 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18722 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18809 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18848 ->
                                 let uu____18849 =
                                   let uu____18850 = is_cons head1 in
                                   Prims.op_Negation uu____18850 in
                                 FStar_Util.Inr uu____18849)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18875 =
                              let uu____18876 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18876.FStar_Syntax_Syntax.n in
                            (match uu____18875 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18894 ->
                                 let uu____18895 =
                                   let uu____18896 = is_cons head1 in
                                   Prims.op_Negation uu____18896 in
                                 FStar_Util.Inr uu____18895))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18965)::rest_a,(p1,uu____18968)::rest_p) ->
                       let uu____19012 = matches_pat t1 p1 in
                       (match uu____19012 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19061 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19167 = matches_pat scrutinee1 p1 in
                       (match uu____19167 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19207  ->
                                  let uu____19208 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____19209 =
                                    let uu____19210 =
                                      FStar_List.map
                                        (fun uu____19220  ->
                                           match uu____19220 with
                                           | (uu____19225,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____19210
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19208 uu____19209);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19256  ->
                                       match uu____19256 with
                                       | (bv,t1) ->
                                           let uu____19279 =
                                             let uu____19286 =
                                               let uu____19289 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____19289 in
                                             let uu____19290 =
                                               let uu____19291 =
                                                 let uu____19322 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____19322, false) in
                                               Clos uu____19291 in
                                             (uu____19286, uu____19290) in
                                           uu____19279 :: env2) env1 s in
                              let uu____19431 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____19431))) in
                 let uu____19432 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____19432
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___203_19453  ->
                match uu___203_19453 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____19457 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____19463 -> d in
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
            let uu___275_19488 = config s e in
            {
              steps = (uu___275_19488.steps);
              tcenv = (uu___275_19488.tcenv);
              delta_level = (uu___275_19488.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___275_19488.strong)
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
      fun t  -> let uu____19513 = config s e in norm_comp uu____19513 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____19526 = config [] env in norm_universe uu____19526 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____19539 = config [] env in ghost_to_pure_aux uu____19539 [] c
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
        let uu____19557 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____19557 in
      let uu____19564 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____19564
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___276_19566 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___276_19566.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___276_19566.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____19569  ->
                    let uu____19570 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____19570))
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
            ((let uu____19587 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19587);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19598 = config [AllowUnboundUniverses] env in
          norm_comp uu____19598 [] c
        with
        | e ->
            ((let uu____19611 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19611);
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
                   let uu____19648 =
                     let uu____19649 =
                       let uu____19656 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____19656) in
                     FStar_Syntax_Syntax.Tm_refine uu____19649 in
                   mk uu____19648 t01.FStar_Syntax_Syntax.pos
               | uu____19661 -> t2)
          | uu____19662 -> t2 in
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
        let uu____19702 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19702 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19731 ->
                 let uu____19738 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19738 with
                  | (actuals,uu____19748,uu____19749) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19763 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19763 with
                         | (binders,args) ->
                             let uu____19780 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19780
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
      | uu____19788 ->
          let uu____19789 = FStar_Syntax_Util.head_and_args t in
          (match uu____19789 with
           | (head1,args) ->
               let uu____19826 =
                 let uu____19827 = FStar_Syntax_Subst.compress head1 in
                 uu____19827.FStar_Syntax_Syntax.n in
               (match uu____19826 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19830,thead) ->
                    let uu____19856 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19856 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19898 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___281_19906 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___281_19906.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___281_19906.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___281_19906.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___281_19906.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___281_19906.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___281_19906.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___281_19906.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___281_19906.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___281_19906.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___281_19906.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___281_19906.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___281_19906.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___281_19906.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___281_19906.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___281_19906.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___281_19906.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___281_19906.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___281_19906.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___281_19906.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___281_19906.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___281_19906.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___281_19906.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___281_19906.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___281_19906.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___281_19906.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___281_19906.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___281_19906.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___281_19906.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___281_19906.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___281_19906.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___281_19906.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19898 with
                            | (uu____19907,ty,uu____19909) ->
                                eta_expand_with_type env t ty))
                | uu____19910 ->
                    let uu____19911 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___282_19919 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___282_19919.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___282_19919.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___282_19919.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___282_19919.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___282_19919.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___282_19919.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___282_19919.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___282_19919.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___282_19919.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___282_19919.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___282_19919.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___282_19919.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___282_19919.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___282_19919.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___282_19919.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___282_19919.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___282_19919.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___282_19919.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___282_19919.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___282_19919.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___282_19919.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___282_19919.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___282_19919.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___282_19919.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___282_19919.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___282_19919.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___282_19919.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___282_19919.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___282_19919.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___282_19919.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___282_19919.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19911 with
                     | (uu____19920,ty,uu____19922) ->
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
            | (uu____19996,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____20002,FStar_Util.Inl t) ->
                let uu____20008 =
                  let uu____20011 =
                    let uu____20012 =
                      let uu____20025 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____20025) in
                    FStar_Syntax_Syntax.Tm_arrow uu____20012 in
                  FStar_Syntax_Syntax.mk uu____20011 in
                uu____20008 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____20029 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____20029 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____20056 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____20111 ->
                    let uu____20112 =
                      let uu____20121 =
                        let uu____20122 = FStar_Syntax_Subst.compress t3 in
                        uu____20122.FStar_Syntax_Syntax.n in
                      (uu____20121, tc) in
                    (match uu____20112 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____20147) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____20184) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____20223,FStar_Util.Inl uu____20224) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____20247 -> failwith "Impossible") in
              (match uu____20056 with
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
          let uu____20352 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____20352 with
          | (univ_names1,binders1,tc) ->
              let uu____20410 = FStar_Util.left tc in
              (univ_names1, binders1, uu____20410)
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
          let uu____20445 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20445 with
          | (univ_names1,binders1,tc) ->
              let uu____20505 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20505)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20538 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20538 with
           | (univ_names1,binders1,typ1) ->
               let uu___283_20566 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_20566.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_20566.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_20566.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_20566.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___284_20587 = s in
          let uu____20588 =
            let uu____20589 =
              let uu____20598 = FStar_List.map (elim_uvars env) sigs in
              (uu____20598, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20589 in
          {
            FStar_Syntax_Syntax.sigel = uu____20588;
            FStar_Syntax_Syntax.sigrng =
              (uu___284_20587.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___284_20587.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___284_20587.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___284_20587.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20615 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20615 with
           | (univ_names1,uu____20633,typ1) ->
               let uu___285_20647 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___285_20647.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___285_20647.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___285_20647.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___285_20647.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20653 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20653 with
           | (univ_names1,uu____20671,typ1) ->
               let uu___286_20685 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___286_20685.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___286_20685.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___286_20685.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___286_20685.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20719 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20719 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20742 =
                            let uu____20743 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20743 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20742 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___287_20746 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___287_20746.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___287_20746.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___288_20747 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___288_20747.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___288_20747.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___288_20747.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___288_20747.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___289_20759 = s in
          let uu____20760 =
            let uu____20761 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20761 in
          {
            FStar_Syntax_Syntax.sigel = uu____20760;
            FStar_Syntax_Syntax.sigrng =
              (uu___289_20759.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___289_20759.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___289_20759.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___289_20759.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20765 = elim_uvars_aux_t env us [] t in
          (match uu____20765 with
           | (us1,uu____20783,t1) ->
               let uu___290_20797 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___290_20797.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___290_20797.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___290_20797.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___290_20797.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20798 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20800 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20800 with
           | (univs1,binders,signature) ->
               let uu____20828 =
                 let uu____20837 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20837 with
                 | (univs_opening,univs2) ->
                     let uu____20864 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20864) in
               (match uu____20828 with
                | (univs_opening,univs_closing) ->
                    let uu____20881 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20887 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20888 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20887, uu____20888) in
                    (match uu____20881 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20910 =
                           match uu____20910 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20928 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20928 with
                                | (us1,t1) ->
                                    let uu____20939 =
                                      let uu____20944 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20951 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20944, uu____20951) in
                                    (match uu____20939 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20964 =
                                           let uu____20969 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20978 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20969, uu____20978) in
                                         (match uu____20964 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20994 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20994 in
                                              let uu____20995 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20995 with
                                               | (uu____21016,uu____21017,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____21032 =
                                                       let uu____21033 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____21033 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____21032 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____21038 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____21038 with
                           | (uu____21051,uu____21052,t1) -> t1 in
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
                             | uu____21112 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____21129 =
                               let uu____21130 =
                                 FStar_Syntax_Subst.compress body in
                               uu____21130.FStar_Syntax_Syntax.n in
                             match uu____21129 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____21189 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____21218 =
                               let uu____21219 =
                                 FStar_Syntax_Subst.compress t in
                               uu____21219.FStar_Syntax_Syntax.n in
                             match uu____21218 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____21240) ->
                                 let uu____21261 = destruct_action_body body in
                                 (match uu____21261 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____21306 ->
                                 let uu____21307 = destruct_action_body t in
                                 (match uu____21307 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____21356 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____21356 with
                           | (action_univs,t) ->
                               let uu____21365 = destruct_action_typ_templ t in
                               (match uu____21365 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___291_21406 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___291_21406.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___291_21406.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___292_21408 = ed in
                           let uu____21409 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____21410 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____21411 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21412 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21413 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21414 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21415 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21416 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21417 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21418 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21419 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21420 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21421 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21422 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___292_21408.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___292_21408.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____21409;
                             FStar_Syntax_Syntax.bind_wp = uu____21410;
                             FStar_Syntax_Syntax.if_then_else = uu____21411;
                             FStar_Syntax_Syntax.ite_wp = uu____21412;
                             FStar_Syntax_Syntax.stronger = uu____21413;
                             FStar_Syntax_Syntax.close_wp = uu____21414;
                             FStar_Syntax_Syntax.assert_p = uu____21415;
                             FStar_Syntax_Syntax.assume_p = uu____21416;
                             FStar_Syntax_Syntax.null_wp = uu____21417;
                             FStar_Syntax_Syntax.trivial = uu____21418;
                             FStar_Syntax_Syntax.repr = uu____21419;
                             FStar_Syntax_Syntax.return_repr = uu____21420;
                             FStar_Syntax_Syntax.bind_repr = uu____21421;
                             FStar_Syntax_Syntax.actions = uu____21422
                           } in
                         let uu___293_21425 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___293_21425.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___293_21425.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___293_21425.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___293_21425.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___204_21442 =
            match uu___204_21442 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21469 = elim_uvars_aux_t env us [] t in
                (match uu____21469 with
                 | (us1,uu____21493,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___294_21512 = sub_eff in
            let uu____21513 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21516 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___294_21512.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___294_21512.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21513;
              FStar_Syntax_Syntax.lift = uu____21516
            } in
          let uu___295_21519 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___295_21519.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___295_21519.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___295_21519.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___295_21519.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____21529 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21529 with
           | (univ_names1,binders1,comp1) ->
               let uu___296_21563 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___296_21563.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___296_21563.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___296_21563.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___296_21563.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21574 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t