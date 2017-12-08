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
      let uu____6155 =
        let uu____6156 =
          let uu____6157 = FStar_Syntax_Syntax.as_arg c in [uu____6157] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6156 in
      uu____6155 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6192 =
              let uu____6205 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6205, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6225  ->
                        fun uu____6226  ->
                          match (uu____6225, uu____6226) with
                          | ((int_to_t1,x),(uu____6245,y)) ->
                              let uu____6255 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6255))) in
            let uu____6256 =
              let uu____6271 =
                let uu____6284 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6284, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6304  ->
                          fun uu____6305  ->
                            match (uu____6304, uu____6305) with
                            | ((int_to_t1,x),(uu____6324,y)) ->
                                let uu____6334 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6334))) in
              let uu____6335 =
                let uu____6350 =
                  let uu____6363 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6363, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6383  ->
                            fun uu____6384  ->
                              match (uu____6383, uu____6384) with
                              | ((int_to_t1,x),(uu____6403,y)) ->
                                  let uu____6413 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6413))) in
                [uu____6350] in
              uu____6271 :: uu____6335 in
            uu____6192 :: uu____6256)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6503)::(a1,uu____6505)::(a2,uu____6507)::[] ->
        let uu____6544 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6544 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_6550 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_6550.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_6550.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6554 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6554.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6554.FStar_Syntax_Syntax.vars)
                })
         | uu____6555 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6557)::uu____6558::(a1,uu____6560)::(a2,uu____6562)::[] ->
        let uu____6611 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6611 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___223_6617 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___223_6617.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___223_6617.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6621 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6621.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6621.FStar_Syntax_Syntax.vars)
                })
         | uu____6622 -> FStar_Pervasives_Native.None)
    | uu____6623 -> failwith "Unexpected number of arguments" in
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
      let uu____6642 =
        let uu____6643 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6643 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6642
    with | uu____6649 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6653 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6653) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6713  ->
           fun subst1  ->
             match uu____6713 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6755)) ->
                      let uu____6814 = b in
                      (match uu____6814 with
                       | (bv,uu____6822) ->
                           let uu____6823 =
                             let uu____6824 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6824 in
                           if uu____6823
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6829 = unembed_binder term1 in
                              match uu____6829 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6836 =
                                      let uu___227_6837 = bv in
                                      let uu____6838 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___227_6837.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___227_6837.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6838
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6836 in
                                  let b_for_x =
                                    let uu____6842 =
                                      let uu____6849 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6849) in
                                    FStar_Syntax_Syntax.NT uu____6842 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___194_6858  ->
                                         match uu___194_6858 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6859,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6861;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6862;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6867 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6868 -> subst1)) env []
let reduce_primops:
  'Auu____6885 'Auu____6886 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6886) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6885 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6927 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6927
          then tm
          else
            (let uu____6929 = FStar_Syntax_Util.head_and_args tm in
             match uu____6929 with
             | (head1,args) ->
                 let uu____6966 =
                   let uu____6967 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6967.FStar_Syntax_Syntax.n in
                 (match uu____6966 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6971 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6971 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6988  ->
                                   let uu____6989 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6990 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6997 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6989 uu____6990 uu____6997);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7002  ->
                                   let uu____7003 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7003);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7006  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7008 =
                                 prim_step.interpretation psc args in
                               match uu____7008 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7014  ->
                                         let uu____7015 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7015);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7021  ->
                                         let uu____7022 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7023 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7022 uu____7023);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7024 ->
                           (log_primops cfg
                              (fun uu____7028  ->
                                 let uu____7029 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7029);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7033  ->
                            let uu____7034 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7034);
                       (match args with
                        | (a1,uu____7036)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7053 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7065  ->
                            let uu____7066 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7066);
                       (match args with
                        | (a1,uu____7068)::(a2,uu____7070)::[] ->
                            let uu____7097 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____7097 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___228_7101 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___228_7101.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___228_7101.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7104 -> tm))
                  | uu____7113 -> tm))
let reduce_equality:
  'Auu____7118 'Auu____7119 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7119) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7118 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___229_7157 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___229_7157.tcenv);
           delta_level = (uu___229_7157.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___229_7157.strong)
         }) tm
let maybe_simplify_aux:
  'Auu____7164 'Auu____7165 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7165) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7164 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7207 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7207
          then tm1
          else
            (let w t =
               let uu___230_7219 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___230_7219.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___230_7219.FStar_Syntax_Syntax.vars)
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
               | uu____7236 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7241 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7241
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7262 =
                 match uu____7262 with
                 | (t1,q) ->
                     let uu____7275 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7275 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7303 -> (t1, q)) in
               let uu____7312 = FStar_Syntax_Util.head_and_args t in
               match uu____7312 with
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
                         FStar_Syntax_Syntax.pos = uu____7409;
                         FStar_Syntax_Syntax.vars = uu____7410;_},uu____7411);
                    FStar_Syntax_Syntax.pos = uu____7412;
                    FStar_Syntax_Syntax.vars = uu____7413;_},args)
                 ->
                 let uu____7439 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7439
                 then
                   let uu____7440 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7440 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7495)::
                        (uu____7496,(arg,uu____7498))::[] ->
                        maybe_auto_squash arg
                    | (uu____7563,(arg,uu____7565))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7566)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7631)::uu____7632::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7695::(FStar_Pervasives_Native.Some (false
                                   ),uu____7696)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7759 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7775 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7775
                    then
                      let uu____7776 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7776 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7831)::uu____7832::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7895::(FStar_Pervasives_Native.Some (true
                                     ),uu____7896)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7959)::
                          (uu____7960,(arg,uu____7962))::[] ->
                          maybe_auto_squash arg
                      | (uu____8027,(arg,uu____8029))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8030)::[]
                          -> maybe_auto_squash arg
                      | uu____8095 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8111 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8111
                       then
                         let uu____8112 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8112 with
                         | uu____8167::(FStar_Pervasives_Native.Some (true
                                        ),uu____8168)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8231)::uu____8232::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8295)::
                             (uu____8296,(arg,uu____8298))::[] ->
                             maybe_auto_squash arg
                         | (uu____8363,(p,uu____8365))::(uu____8366,(q,uu____8368))::[]
                             ->
                             let uu____8433 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8433
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8435 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8451 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8451
                          then
                            let uu____8452 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8452 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8507)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8546)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8585 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8601 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8601
                             then
                               match args with
                               | (t,uu____8603)::[] ->
                                   let uu____8620 =
                                     let uu____8621 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8621.FStar_Syntax_Syntax.n in
                                   (match uu____8620 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8624::[],body,uu____8626) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8653 -> tm1)
                                    | uu____8656 -> tm1)
                               | (uu____8657,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8658))::
                                   (t,uu____8660)::[] ->
                                   let uu____8699 =
                                     let uu____8700 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8700.FStar_Syntax_Syntax.n in
                                   (match uu____8699 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8703::[],body,uu____8705) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8732 -> tm1)
                                    | uu____8735 -> tm1)
                               | uu____8736 -> tm1
                             else
                               (let uu____8746 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8746
                                then
                                  match args with
                                  | (t,uu____8748)::[] ->
                                      let uu____8765 =
                                        let uu____8766 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8766.FStar_Syntax_Syntax.n in
                                      (match uu____8765 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8769::[],body,uu____8771)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8798 -> tm1)
                                       | uu____8801 -> tm1)
                                  | (uu____8802,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8803))::(t,uu____8805)::[] ->
                                      let uu____8844 =
                                        let uu____8845 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8845.FStar_Syntax_Syntax.n in
                                      (match uu____8844 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8848::[],body,uu____8850)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8877 -> tm1)
                                       | uu____8880 -> tm1)
                                  | uu____8881 -> tm1
                                else
                                  (let uu____8891 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8891
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8892;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8893;_},uu____8894)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8911;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8912;_},uu____8913)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8930 -> tm1
                                   else
                                     (let uu____8940 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8940 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8960 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8970;
                    FStar_Syntax_Syntax.vars = uu____8971;_},args)
                 ->
                 let uu____8993 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8993
                 then
                   let uu____8994 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8994 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9049)::
                        (uu____9050,(arg,uu____9052))::[] ->
                        maybe_auto_squash arg
                    | (uu____9117,(arg,uu____9119))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9120)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9185)::uu____9186::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9249::(FStar_Pervasives_Native.Some (false
                                   ),uu____9250)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9313 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9329 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9329
                    then
                      let uu____9330 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9330 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9385)::uu____9386::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9449::(FStar_Pervasives_Native.Some (true
                                     ),uu____9450)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9513)::
                          (uu____9514,(arg,uu____9516))::[] ->
                          maybe_auto_squash arg
                      | (uu____9581,(arg,uu____9583))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9584)::[]
                          -> maybe_auto_squash arg
                      | uu____9649 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9665 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9665
                       then
                         let uu____9666 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9666 with
                         | uu____9721::(FStar_Pervasives_Native.Some (true
                                        ),uu____9722)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9785)::uu____9786::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9849)::
                             (uu____9850,(arg,uu____9852))::[] ->
                             maybe_auto_squash arg
                         | (uu____9917,(p,uu____9919))::(uu____9920,(q,uu____9922))::[]
                             ->
                             let uu____9987 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9987
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9989 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10005 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10005
                          then
                            let uu____10006 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10006 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10061)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10100)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10139 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10155 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10155
                             then
                               match args with
                               | (t,uu____10157)::[] ->
                                   let uu____10174 =
                                     let uu____10175 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10175.FStar_Syntax_Syntax.n in
                                   (match uu____10174 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10178::[],body,uu____10180) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10207 -> tm1)
                                    | uu____10210 -> tm1)
                               | (uu____10211,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10212))::
                                   (t,uu____10214)::[] ->
                                   let uu____10253 =
                                     let uu____10254 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10254.FStar_Syntax_Syntax.n in
                                   (match uu____10253 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10257::[],body,uu____10259) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10286 -> tm1)
                                    | uu____10289 -> tm1)
                               | uu____10290 -> tm1
                             else
                               (let uu____10300 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10300
                                then
                                  match args with
                                  | (t,uu____10302)::[] ->
                                      let uu____10319 =
                                        let uu____10320 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10320.FStar_Syntax_Syntax.n in
                                      (match uu____10319 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10323::[],body,uu____10325)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10352 -> tm1)
                                       | uu____10355 -> tm1)
                                  | (uu____10356,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10357))::(t,uu____10359)::[] ->
                                      let uu____10398 =
                                        let uu____10399 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10399.FStar_Syntax_Syntax.n in
                                      (match uu____10398 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10402::[],body,uu____10404)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10431 -> tm1)
                                       | uu____10434 -> tm1)
                                  | uu____10435 -> tm1
                                else
                                  (let uu____10445 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10445
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10446;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10447;_},uu____10448)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10465;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10466;_},uu____10467)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10484 -> tm1
                                   else
                                     (let uu____10494 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10494 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10514 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10523 -> tm1)
let maybe_simplify:
  'Auu____10530 'Auu____10531 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10531) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10530 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10574 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10574
           then
             let uu____10575 = FStar_Syntax_Print.term_to_string tm in
             let uu____10576 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10575 uu____10576
           else ());
          tm'
let is_norm_request:
  'Auu____10582 .
    FStar_Syntax_Syntax.term -> 'Auu____10582 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10595 =
        let uu____10602 =
          let uu____10603 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10603.FStar_Syntax_Syntax.n in
        (uu____10602, args) in
      match uu____10595 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10609::uu____10610::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10614::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10619::uu____10620::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10623 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___195_10634  ->
    match uu___195_10634 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10640 =
          let uu____10643 =
            let uu____10644 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10644 in
          [uu____10643] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10640
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10659 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10659) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10697 =
          let uu____10700 =
            let uu____10705 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10705 s in
          FStar_All.pipe_right uu____10700 FStar_Util.must in
        FStar_All.pipe_right uu____10697 tr_norm_steps in
      match args with
      | uu____10730::(tm,uu____10732)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10755)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10770)::uu____10771::(tm,uu____10773)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10813 =
              let uu____10816 = full_norm steps in parse_steps uu____10816 in
            Beta :: uu____10813 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10825 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___196_10842  ->
    match uu___196_10842 with
    | (App
        (uu____10845,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10846;
                       FStar_Syntax_Syntax.vars = uu____10847;_},uu____10848,uu____10849))::uu____10850
        -> true
    | uu____10857 -> false
let firstn:
  'Auu____10863 .
    Prims.int ->
      'Auu____10863 Prims.list ->
        ('Auu____10863 Prims.list,'Auu____10863 Prims.list)
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
          (uu____10899,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10900;
                         FStar_Syntax_Syntax.vars = uu____10901;_},uu____10902,uu____10903))::uu____10904
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10911 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11027  ->
               let uu____11028 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11029 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11030 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11037 =
                 let uu____11038 =
                   let uu____11041 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11041 in
                 stack_to_string uu____11038 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11028 uu____11029 uu____11030 uu____11037);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11064 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11089 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11106 =
                 let uu____11107 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11108 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11107 uu____11108 in
               failwith uu____11106
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11109 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11126 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11127 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11128;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11129;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11132;
                 FStar_Syntax_Syntax.fv_delta = uu____11133;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11134;
                 FStar_Syntax_Syntax.fv_delta = uu____11135;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11136);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11144 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11144 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11150  ->
                     let uu____11151 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11152 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11151 uu____11152);
                if b
                then
                  (let uu____11153 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11153 t1 fv)
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
                 let uu___231_11192 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___231_11192.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___231_11192.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11225 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11225) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___232_11233 = cfg in
                 let uu____11234 =
                   FStar_List.filter
                     (fun uu___197_11237  ->
                        match uu___197_11237 with
                        | UnfoldOnly uu____11238 -> false
                        | NoDeltaSteps  -> false
                        | uu____11241 -> true) cfg.steps in
                 {
                   steps = uu____11234;
                   tcenv = (uu___232_11233.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___232_11233.primitive_steps);
                   strong = (uu___232_11233.strong)
                 } in
               let uu____11242 = get_norm_request (norm cfg' env []) args in
               (match uu____11242 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11258 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___198_11263  ->
                                match uu___198_11263 with
                                | UnfoldUntil uu____11264 -> true
                                | UnfoldOnly uu____11265 -> true
                                | uu____11268 -> false)) in
                      if uu____11258
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___233_11273 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___233_11273.tcenv);
                        delta_level;
                        primitive_steps = (uu___233_11273.primitive_steps);
                        strong = (uu___233_11273.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____11284 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11284
                      then
                        let uu____11287 =
                          let uu____11288 =
                            let uu____11293 = FStar_Util.now () in
                            (t1, uu____11293) in
                          Debug uu____11288 in
                        uu____11287 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11295;
                  FStar_Syntax_Syntax.vars = uu____11296;_},a1::a2::rest)
               ->
               let uu____11344 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11344 with
                | (hd1,uu____11360) ->
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
                  FStar_Syntax_Syntax.pos = uu____11425;
                  FStar_Syntax_Syntax.vars = uu____11426;_},a1::a2::rest)
               ->
               let uu____11474 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11474 with
                | (hd1,uu____11490) ->
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
                  FStar_Syntax_Syntax.pos = uu____11555;
                  FStar_Syntax_Syntax.vars = uu____11556;_},a1::a2::a3::rest)
               ->
               let uu____11617 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11617 with
                | (hd1,uu____11633) ->
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
                    (FStar_Const.Const_reflect uu____11704);
                  FStar_Syntax_Syntax.pos = uu____11705;
                  FStar_Syntax_Syntax.vars = uu____11706;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11738 = FStar_List.tl stack in
               norm cfg env uu____11738 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11741;
                  FStar_Syntax_Syntax.vars = uu____11742;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11774 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11774 with
                | (reify_head,uu____11790) ->
                    let a1 =
                      let uu____11812 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11812 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11815);
                            FStar_Syntax_Syntax.pos = uu____11816;
                            FStar_Syntax_Syntax.vars = uu____11817;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11851 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11861 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11861
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11868 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11868
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11871 =
                      let uu____11878 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11878, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11871 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___199_11891  ->
                         match uu___199_11891 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11894 =
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
                 if uu____11894
                 then false
                 else
                   (let uu____11896 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___200_11903  ->
                              match uu___200_11903 with
                              | UnfoldOnly uu____11904 -> true
                              | uu____11907 -> false)) in
                    match uu____11896 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11911 -> should_delta) in
               (log cfg
                  (fun uu____11919  ->
                     let uu____11920 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11921 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11922 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11920 uu____11921 uu____11922);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11925 = lookup_bvar env x in
               (match uu____11925 with
                | Univ uu____11928 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11977 = FStar_ST.op_Bang r in
                      (match uu____11977 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12116  ->
                                 let uu____12117 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12118 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12117
                                   uu____12118);
                            (let uu____12119 =
                               let uu____12120 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12120.FStar_Syntax_Syntax.n in
                             match uu____12119 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12123 ->
                                 norm cfg env2 stack t'
                             | uu____12140 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12198)::uu____12199 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12208)::uu____12209 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12219,uu____12220))::stack_rest ->
                    (match c with
                     | Univ uu____12224 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12233 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12254  ->
                                    let uu____12255 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12255);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12295  ->
                                    let uu____12296 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12296);
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
                      (let uu___234_12346 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___234_12346.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___234_12346.strong)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12379  ->
                          let uu____12380 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12380);
                     norm cfg env stack1 t1)
                | (Debug uu____12381)::uu____12382 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12389 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12389
                    else
                      (let uu____12391 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12391 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12433  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12461 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12461
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12471 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12471)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12476 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12476.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12476.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12477 -> lopt in
                           (log cfg
                              (fun uu____12483  ->
                                 let uu____12484 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12484);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12497 = cfg in
                               {
                                 steps = (uu___236_12497.steps);
                                 tcenv = (uu___236_12497.tcenv);
                                 delta_level = (uu___236_12497.delta_level);
                                 primitive_steps =
                                   (uu___236_12497.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12508)::uu____12509 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12516 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12516
                    else
                      (let uu____12518 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12518 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12560  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12588 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12588
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12598 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12598)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12603 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12603.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12603.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12604 -> lopt in
                           (log cfg
                              (fun uu____12610  ->
                                 let uu____12611 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12611);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12624 = cfg in
                               {
                                 steps = (uu___236_12624.steps);
                                 tcenv = (uu___236_12624.tcenv);
                                 delta_level = (uu___236_12624.delta_level);
                                 primitive_steps =
                                   (uu___236_12624.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12635)::uu____12636 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12647 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12647
                    else
                      (let uu____12649 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12649 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12691  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12719 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12719
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12729 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12729)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12734 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12734.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12734.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12735 -> lopt in
                           (log cfg
                              (fun uu____12741  ->
                                 let uu____12742 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12742);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12755 = cfg in
                               {
                                 steps = (uu___236_12755.steps);
                                 tcenv = (uu___236_12755.tcenv);
                                 delta_level = (uu___236_12755.delta_level);
                                 primitive_steps =
                                   (uu___236_12755.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12766)::uu____12767 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12778 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12778
                    else
                      (let uu____12780 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12780 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12822  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12850 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12850
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12860 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12860)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12865 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12865.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12865.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12866 -> lopt in
                           (log cfg
                              (fun uu____12872  ->
                                 let uu____12873 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12873);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_12886 = cfg in
                               {
                                 steps = (uu___236_12886.steps);
                                 tcenv = (uu___236_12886.tcenv);
                                 delta_level = (uu___236_12886.delta_level);
                                 primitive_steps =
                                   (uu___236_12886.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12897)::uu____12898 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12913 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12913
                    else
                      (let uu____12915 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12915 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12957  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12985 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12985
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12995 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12995)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13000 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13000.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13000.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13001 -> lopt in
                           (log cfg
                              (fun uu____13007  ->
                                 let uu____13008 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13008);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13021 = cfg in
                               {
                                 steps = (uu___236_13021.steps);
                                 tcenv = (uu___236_13021.tcenv);
                                 delta_level = (uu___236_13021.delta_level);
                                 primitive_steps =
                                   (uu___236_13021.primitive_steps);
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
                      let uu____13032 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13032
                    else
                      (let uu____13034 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13034 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13076  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13104 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13104
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13114 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13114)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_13119 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_13119.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_13119.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13120 -> lopt in
                           (log cfg
                              (fun uu____13126  ->
                                 let uu____13127 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13127);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___236_13140 = cfg in
                               {
                                 steps = (uu___236_13140.steps);
                                 tcenv = (uu___236_13140.tcenv);
                                 delta_level = (uu___236_13140.delta_level);
                                 primitive_steps =
                                   (uu___236_13140.primitive_steps);
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
                      (fun uu____13189  ->
                         fun stack1  ->
                           match uu____13189 with
                           | (a,aq) ->
                               let uu____13201 =
                                 let uu____13202 =
                                   let uu____13209 =
                                     let uu____13210 =
                                       let uu____13241 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13241, false) in
                                     Clos uu____13210 in
                                   (uu____13209, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13202 in
                               uu____13201 :: stack1) args) in
               (log cfg
                  (fun uu____13317  ->
                     let uu____13318 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13318);
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
                             ((let uu___237_13354 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___237_13354.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___237_13354.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13355 ->
                      let uu____13360 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13360)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13363 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13363 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13394 =
                          let uu____13395 =
                            let uu____13402 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___238_13404 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___238_13404.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___238_13404.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13402) in
                          FStar_Syntax_Syntax.Tm_refine uu____13395 in
                        mk uu____13394 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13423 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13423
               else
                 (let uu____13425 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13425 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13433 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13457  -> dummy :: env1) env) in
                        norm_comp cfg uu____13433 c1 in
                      let t2 =
                        let uu____13479 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13479 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13538)::uu____13539 ->
                    (log cfg
                       (fun uu____13550  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13551)::uu____13552 ->
                    (log cfg
                       (fun uu____13563  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13564,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13565;
                                   FStar_Syntax_Syntax.vars = uu____13566;_},uu____13567,uu____13568))::uu____13569
                    ->
                    (log cfg
                       (fun uu____13578  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13579)::uu____13580 ->
                    (log cfg
                       (fun uu____13591  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13592 ->
                    (log cfg
                       (fun uu____13595  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13599  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13616 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13616
                         | FStar_Util.Inr c ->
                             let uu____13624 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13624 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Steps (s,ps,dl))::stack1 ->
                           let t2 =
                             let uu____13647 =
                               let uu____13648 =
                                 let uu____13675 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13675, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13648 in
                             mk uu____13647 t1.FStar_Syntax_Syntax.pos in
                           norm
                             (let uu___239_13696 = cfg in
                              {
                                steps = s;
                                tcenv = (uu___239_13696.tcenv);
                                delta_level = dl;
                                primitive_steps = ps;
                                strong = (uu___239_13696.strong)
                              }) env stack1 t2
                       | uu____13697 ->
                           let uu____13698 =
                             let uu____13699 =
                               let uu____13700 =
                                 let uu____13727 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13727, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13700 in
                             mk uu____13699 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13698))))
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
                         let uu____13837 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13837 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___240_13857 = cfg in
                               let uu____13858 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___240_13857.steps);
                                 tcenv = uu____13858;
                                 delta_level = (uu___240_13857.delta_level);
                                 primitive_steps =
                                   (uu___240_13857.primitive_steps);
                                 strong = (uu___240_13857.strong)
                               } in
                             let norm1 t2 =
                               let uu____13863 =
                                 let uu____13864 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13864 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13863 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___241_13867 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___241_13867.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___241_13867.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13868 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13868
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13879,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13880;
                               FStar_Syntax_Syntax.lbunivs = uu____13881;
                               FStar_Syntax_Syntax.lbtyp = uu____13882;
                               FStar_Syntax_Syntax.lbeff = uu____13883;
                               FStar_Syntax_Syntax.lbdef = uu____13884;_}::uu____13885),uu____13886)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13922 =
                 (let uu____13925 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13925) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13927 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13927))) in
               if uu____13922
               then
                 let binder =
                   let uu____13929 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13929 in
                 let env1 =
                   let uu____13939 =
                     let uu____13946 =
                       let uu____13947 =
                         let uu____13978 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13978,
                           false) in
                       Clos uu____13947 in
                     ((FStar_Pervasives_Native.Some binder), uu____13946) in
                   uu____13939 :: env in
                 (log cfg
                    (fun uu____14063  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____14065 =
                    let uu____14070 =
                      let uu____14071 =
                        let uu____14072 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14072
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14071] in
                    FStar_Syntax_Subst.open_term uu____14070 body in
                  match uu____14065 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____14081  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____14089 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____14089 in
                          FStar_Util.Inl
                            (let uu___242_14099 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___242_14099.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___242_14099.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____14102  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___243_14104 = lb in
                           let uu____14105 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___243_14104.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___243_14104.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____14105
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____14140  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___244_14160 = cfg in
                           {
                             steps = (uu___244_14160.steps);
                             tcenv = (uu___244_14160.tcenv);
                             delta_level = (uu___244_14160.delta_level);
                             primitive_steps =
                               (uu___244_14160.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____14163  ->
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
               let uu____14180 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14180 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14216 =
                               let uu___245_14217 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___245_14217.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___245_14217.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14216 in
                           let uu____14218 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14218 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14244 =
                                   FStar_List.map (fun uu____14260  -> dummy)
                                     lbs1 in
                                 let uu____14261 =
                                   let uu____14270 =
                                     FStar_List.map
                                       (fun uu____14290  -> dummy) xs1 in
                                   FStar_List.append uu____14270 env in
                                 FStar_List.append uu____14244 uu____14261 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14314 =
                                       let uu___246_14315 = rc in
                                       let uu____14316 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___246_14315.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14316;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___246_14315.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14314
                                 | uu____14323 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___247_14327 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___247_14327.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___247_14327.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14337 =
                        FStar_List.map (fun uu____14353  -> dummy) lbs2 in
                      FStar_List.append uu____14337 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14361 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14361 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___248_14377 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___248_14377.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___248_14377.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14404 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14404
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14423 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14499  ->
                        match uu____14499 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___249_14620 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___249_14620.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___249_14620.FStar_Syntax_Syntax.sort)
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
               (match uu____14423 with
                | (rec_env,memos,uu____14817) ->
                    let uu____14870 =
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
                             let uu____15407 =
                               let uu____15414 =
                                 let uu____15415 =
                                   let uu____15446 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15446, false) in
                                 Clos uu____15415 in
                               (FStar_Pervasives_Native.None, uu____15414) in
                             uu____15407 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15551 =
                      let uu____15552 = should_reify cfg stack in
                      Prims.op_Negation uu____15552 in
                    if uu____15551
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____15562 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15562
                        then
                          let uu___250_15563 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___250_15563.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___250_15563.primitive_steps);
                            strong = (uu___250_15563.strong)
                          }
                        else
                          (let uu___251_15565 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___251_15565.tcenv);
                             delta_level = (uu___251_15565.delta_level);
                             primitive_steps =
                               (uu___251_15565.primitive_steps);
                             strong = (uu___251_15565.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15567 =
                         let uu____15568 = FStar_Syntax_Subst.compress head1 in
                         uu____15568.FStar_Syntax_Syntax.n in
                       match uu____15567 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15586 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15586 with
                            | (uu____15587,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15593 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15601 =
                                         let uu____15602 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15602.FStar_Syntax_Syntax.n in
                                       match uu____15601 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15608,uu____15609))
                                           ->
                                           let uu____15618 =
                                             let uu____15619 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15619.FStar_Syntax_Syntax.n in
                                           (match uu____15618 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15625,msrc,uu____15627))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15636 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15636
                                            | uu____15637 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15638 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15639 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15639 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___252_15644 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___252_15644.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___252_15644.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___252_15644.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15645 =
                                            FStar_List.tl stack in
                                          let uu____15646 =
                                            let uu____15647 =
                                              let uu____15650 =
                                                let uu____15651 =
                                                  let uu____15664 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15664) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15651 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15650 in
                                            uu____15647
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15645
                                            uu____15646
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15680 =
                                            let uu____15681 = is_return body in
                                            match uu____15681 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15685;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15686;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15691 -> false in
                                          if uu____15680
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
                                               let uu____15715 =
                                                 let uu____15718 =
                                                   let uu____15719 =
                                                     let uu____15736 =
                                                       let uu____15739 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15739] in
                                                     (uu____15736, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15719 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15718 in
                                               uu____15715
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15755 =
                                                 let uu____15756 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15756.FStar_Syntax_Syntax.n in
                                               match uu____15755 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15762::uu____15763::[])
                                                   ->
                                                   let uu____15770 =
                                                     let uu____15773 =
                                                       let uu____15774 =
                                                         let uu____15781 =
                                                           let uu____15784 =
                                                             let uu____15785
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15785 in
                                                           let uu____15786 =
                                                             let uu____15789
                                                               =
                                                               let uu____15790
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15790 in
                                                             [uu____15789] in
                                                           uu____15784 ::
                                                             uu____15786 in
                                                         (bind1, uu____15781) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15774 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15773 in
                                                   uu____15770
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15798 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15804 =
                                                 let uu____15807 =
                                                   let uu____15808 =
                                                     let uu____15823 =
                                                       let uu____15826 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15827 =
                                                         let uu____15830 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15831 =
                                                           let uu____15834 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15835 =
                                                             let uu____15838
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15839
                                                               =
                                                               let uu____15842
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15843
                                                                 =
                                                                 let uu____15846
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15846] in
                                                               uu____15842 ::
                                                                 uu____15843 in
                                                             uu____15838 ::
                                                               uu____15839 in
                                                           uu____15834 ::
                                                             uu____15835 in
                                                         uu____15830 ::
                                                           uu____15831 in
                                                       uu____15826 ::
                                                         uu____15827 in
                                                     (bind_inst, uu____15823) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15808 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15807 in
                                               uu____15804
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15854 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____15854 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15878 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15878 with
                            | (uu____15879,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15914 =
                                        let uu____15915 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15915.FStar_Syntax_Syntax.n in
                                      match uu____15914 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15921) -> t4
                                      | uu____15926 -> head2 in
                                    let uu____15927 =
                                      let uu____15928 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15928.FStar_Syntax_Syntax.n in
                                    match uu____15927 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15934 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15935 = maybe_extract_fv head2 in
                                  match uu____15935 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15945 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15945
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15950 =
                                          maybe_extract_fv head3 in
                                        match uu____15950 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15955 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15956 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15961 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15976 =
                                    match uu____15976 with
                                    | (e,q) ->
                                        let uu____15983 =
                                          let uu____15984 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15984.FStar_Syntax_Syntax.n in
                                        (match uu____15983 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15999 -> false) in
                                  let uu____16000 =
                                    let uu____16001 =
                                      let uu____16008 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____16008 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____16001 in
                                  if uu____16000
                                  then
                                    let uu____16013 =
                                      let uu____16014 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____16014 in
                                    failwith uu____16013
                                  else ());
                                 (let uu____16016 =
                                    maybe_unfold_action head_app in
                                  match uu____16016 with
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
                                      let uu____16055 = FStar_List.tl stack in
                                      norm cfg env uu____16055 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16069 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16069 in
                           let uu____16070 = FStar_List.tl stack in
                           norm cfg env uu____16070 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16191  ->
                                     match uu____16191 with
                                     | (pat,wopt,tm) ->
                                         let uu____16239 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16239))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16271 = FStar_List.tl stack in
                           norm cfg env uu____16271 tm
                       | uu____16272 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16280 = should_reify cfg stack in
                    if uu____16280
                    then
                      let uu____16281 = FStar_List.tl stack in
                      let uu____16282 =
                        let uu____16283 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16283 in
                      norm cfg env uu____16281 uu____16282
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16286 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16286
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___253_16295 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___253_16295.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___253_16295.primitive_steps);
                             strong = (uu___253_16295.strong)
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
                | uu____16297 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____16299::uu____16300 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16305) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16306 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____16337 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16351 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16351
                             | uu____16362 -> m in
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
              let uu____16374 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16374 in
            let uu____16375 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16375 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16388  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16399  ->
                      let uu____16400 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16401 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16400
                        uu____16401);
                 (let t1 =
                    let uu____16403 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16403
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
                    | (UnivArgs (us',uu____16413))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____16468 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____16471 ->
                        let uu____16474 =
                          let uu____16475 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16475 in
                        failwith uu____16474
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
              let uu____16485 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16485 with
              | (uu____16486,return_repr) ->
                  let return_inst =
                    let uu____16495 =
                      let uu____16496 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16496.FStar_Syntax_Syntax.n in
                    match uu____16495 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16502::[]) ->
                        let uu____16509 =
                          let uu____16512 =
                            let uu____16513 =
                              let uu____16520 =
                                let uu____16523 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16523] in
                              (return_tm, uu____16520) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16513 in
                          FStar_Syntax_Syntax.mk uu____16512 in
                        uu____16509 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16531 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16534 =
                    let uu____16537 =
                      let uu____16538 =
                        let uu____16553 =
                          let uu____16556 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16557 =
                            let uu____16560 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16560] in
                          uu____16556 :: uu____16557 in
                        (return_inst, uu____16553) in
                      FStar_Syntax_Syntax.Tm_app uu____16538 in
                    FStar_Syntax_Syntax.mk uu____16537 in
                  uu____16534 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16569 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16569 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16572 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16572
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16573;
                     FStar_TypeChecker_Env.mtarget = uu____16574;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16575;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16590;
                     FStar_TypeChecker_Env.mtarget = uu____16591;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16592;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16616 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16617 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16616 t FStar_Syntax_Syntax.tun uu____16617)
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
                (fun uu____16673  ->
                   match uu____16673 with
                   | (a,imp) ->
                       let uu____16684 = norm cfg env [] a in
                       (uu____16684, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___254_16701 = comp1 in
            let uu____16704 =
              let uu____16705 =
                let uu____16714 = norm cfg env [] t in
                let uu____16715 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16714, uu____16715) in
              FStar_Syntax_Syntax.Total uu____16705 in
            {
              FStar_Syntax_Syntax.n = uu____16704;
              FStar_Syntax_Syntax.pos =
                (uu___254_16701.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___254_16701.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___255_16730 = comp1 in
            let uu____16733 =
              let uu____16734 =
                let uu____16743 = norm cfg env [] t in
                let uu____16744 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16743, uu____16744) in
              FStar_Syntax_Syntax.GTotal uu____16734 in
            {
              FStar_Syntax_Syntax.n = uu____16733;
              FStar_Syntax_Syntax.pos =
                (uu___255_16730.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___255_16730.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16796  ->
                      match uu____16796 with
                      | (a,i) ->
                          let uu____16807 = norm cfg env [] a in
                          (uu____16807, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___201_16818  ->
                      match uu___201_16818 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16822 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16822
                      | f -> f)) in
            let uu___256_16826 = comp1 in
            let uu____16829 =
              let uu____16830 =
                let uu___257_16831 = ct in
                let uu____16832 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16833 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16836 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16832;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___257_16831.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16833;
                  FStar_Syntax_Syntax.effect_args = uu____16836;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16830 in
            {
              FStar_Syntax_Syntax.n = uu____16829;
              FStar_Syntax_Syntax.pos =
                (uu___256_16826.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___256_16826.FStar_Syntax_Syntax.vars)
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
            (let uu___258_16854 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___258_16854.tcenv);
               delta_level = (uu___258_16854.delta_level);
               primitive_steps = (uu___258_16854.primitive_steps);
               strong = (uu___258_16854.strong)
             }) env [] t in
        let non_info t =
          let uu____16859 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16859 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16862 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___259_16881 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___259_16881.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___259_16881.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16888 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16888
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
                    let uu___260_16899 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___260_16899.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___260_16899.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___260_16899.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___261_16901 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___261_16901.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___261_16901.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___261_16901.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___261_16901.FStar_Syntax_Syntax.flags)
                    } in
              let uu___262_16902 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___262_16902.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___262_16902.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16904 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16907  ->
        match uu____16907 with
        | (x,imp) ->
            let uu____16910 =
              let uu___263_16911 = x in
              let uu____16912 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___263_16911.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___263_16911.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16912
              } in
            (uu____16910, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16918 =
          FStar_List.fold_left
            (fun uu____16936  ->
               fun b  ->
                 match uu____16936 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16918 with | (nbs,uu____16976) -> FStar_List.rev nbs
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
            let uu____16992 =
              let uu___264_16993 = rc in
              let uu____16994 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___264_16993.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16994;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___264_16993.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16992
        | uu____17001 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17014  ->
               let uu____17015 = FStar_Syntax_Print.tag_of_term t in
               let uu____17016 = FStar_Syntax_Print.term_to_string t in
               let uu____17017 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17024 =
                 let uu____17025 =
                   let uu____17028 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17028 in
                 stack_to_string uu____17025 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____17015 uu____17016 uu____17017 uu____17024);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____17057 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____17057
                 then
                   let time_now = FStar_Util.now () in
                   let uu____17059 =
                     let uu____17060 =
                       let uu____17061 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17061 in
                     FStar_Util.string_of_int uu____17060 in
                   let uu____17066 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17067 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17059 uu____17066 uu____17067
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___265_17085 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___265_17085.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___265_17085.strong)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____17126  ->
                     let uu____17127 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17127);
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
               let uu____17163 =
                 let uu___266_17164 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___266_17164.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___266_17164.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____17163
           | (Arg (Univ uu____17165,uu____17166,uu____17167))::uu____17168 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17171,uu____17172))::uu____17173 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____17189),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17242  ->
                     let uu____17243 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17243);
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
                  (let uu____17253 = FStar_ST.op_Bang m in
                   match uu____17253 with
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
                   | FStar_Pervasives_Native.Some (uu____17399,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17442 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17442
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17454  ->
                     let uu____17455 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17455);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17460 =
                   log cfg
                     (fun uu____17465  ->
                        let uu____17466 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17467 =
                          let uu____17468 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17485  ->
                                    match uu____17485 with
                                    | (p,uu____17495,uu____17496) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17468
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17466 uu____17467);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___202_17513  ->
                                match uu___202_17513 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17514 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___267_17518 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___267_17518.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___267_17518.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17550 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17571 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17631  ->
                                    fun uu____17632  ->
                                      match (uu____17631, uu____17632) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17723 = norm_pat env3 p1 in
                                          (match uu____17723 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17571 with
                           | (pats1,env3) ->
                               ((let uu___268_17805 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___268_17805.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___269_17824 = x in
                            let uu____17825 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___269_17824.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___269_17824.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17825
                            } in
                          ((let uu___270_17839 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___270_17839.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___271_17850 = x in
                            let uu____17851 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___271_17850.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___271_17850.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17851
                            } in
                          ((let uu___272_17865 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___272_17865.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___273_17881 = x in
                            let uu____17882 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___273_17881.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___273_17881.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17882
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___274_17889 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___274_17889.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17899 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17913 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17913 with
                                  | (p,wopt,e) ->
                                      let uu____17933 = norm_pat env1 p in
                                      (match uu____17933 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17958 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17958 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17964 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17964) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17974) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17979 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17980;
                         FStar_Syntax_Syntax.fv_delta = uu____17981;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17982;
                         FStar_Syntax_Syntax.fv_delta = uu____17983;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17984);_}
                       -> true
                   | uu____17991 -> false in
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
                   let uu____18136 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18136 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18223 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18262 ->
                                 let uu____18263 =
                                   let uu____18264 = is_cons head1 in
                                   Prims.op_Negation uu____18264 in
                                 FStar_Util.Inr uu____18263)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18289 =
                              let uu____18290 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18290.FStar_Syntax_Syntax.n in
                            (match uu____18289 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18308 ->
                                 let uu____18309 =
                                   let uu____18310 = is_cons head1 in
                                   Prims.op_Negation uu____18310 in
                                 FStar_Util.Inr uu____18309))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18379)::rest_a,(p1,uu____18382)::rest_p) ->
                       let uu____18426 = matches_pat t1 p1 in
                       (match uu____18426 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18475 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18581 = matches_pat scrutinee1 p1 in
                       (match uu____18581 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18621  ->
                                  let uu____18622 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18623 =
                                    let uu____18624 =
                                      FStar_List.map
                                        (fun uu____18634  ->
                                           match uu____18634 with
                                           | (uu____18639,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18624
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18622 uu____18623);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18670  ->
                                       match uu____18670 with
                                       | (bv,t1) ->
                                           let uu____18693 =
                                             let uu____18700 =
                                               let uu____18703 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18703 in
                                             let uu____18704 =
                                               let uu____18705 =
                                                 let uu____18736 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18736, false) in
                                               Clos uu____18705 in
                                             (uu____18700, uu____18704) in
                                           uu____18693 :: env2) env1 s in
                              let uu____18845 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18845))) in
                 let uu____18846 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18846
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___203_18867  ->
                match uu___203_18867 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18871 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18877 -> d in
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
            let uu___275_18902 = config s e in
            {
              steps = (uu___275_18902.steps);
              tcenv = (uu___275_18902.tcenv);
              delta_level = (uu___275_18902.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___275_18902.strong)
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
      fun t  -> let uu____18927 = config s e in norm_comp uu____18927 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18940 = config [] env in norm_universe uu____18940 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18953 = config [] env in ghost_to_pure_aux uu____18953 [] c
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
        let uu____18971 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18971 in
      let uu____18978 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18978
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___276_18980 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___276_18980.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___276_18980.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18983  ->
                    let uu____18984 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18984))
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
            ((let uu____19001 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19001);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19012 = config [AllowUnboundUniverses] env in
          norm_comp uu____19012 [] c
        with
        | e ->
            ((let uu____19025 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19025);
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
                   let uu____19062 =
                     let uu____19063 =
                       let uu____19070 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____19070) in
                     FStar_Syntax_Syntax.Tm_refine uu____19063 in
                   mk uu____19062 t01.FStar_Syntax_Syntax.pos
               | uu____19075 -> t2)
          | uu____19076 -> t2 in
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
        let uu____19116 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19116 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19145 ->
                 let uu____19152 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19152 with
                  | (actuals,uu____19162,uu____19163) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19177 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19177 with
                         | (binders,args) ->
                             let uu____19194 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19194
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
      | uu____19202 ->
          let uu____19203 = FStar_Syntax_Util.head_and_args t in
          (match uu____19203 with
           | (head1,args) ->
               let uu____19240 =
                 let uu____19241 = FStar_Syntax_Subst.compress head1 in
                 uu____19241.FStar_Syntax_Syntax.n in
               (match uu____19240 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19244,thead) ->
                    let uu____19270 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19270 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19312 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___281_19320 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___281_19320.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___281_19320.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___281_19320.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___281_19320.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___281_19320.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___281_19320.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___281_19320.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___281_19320.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___281_19320.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___281_19320.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___281_19320.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___281_19320.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___281_19320.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___281_19320.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___281_19320.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___281_19320.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___281_19320.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___281_19320.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___281_19320.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___281_19320.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___281_19320.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___281_19320.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___281_19320.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___281_19320.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___281_19320.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___281_19320.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___281_19320.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___281_19320.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___281_19320.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___281_19320.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___281_19320.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19312 with
                            | (uu____19321,ty,uu____19323) ->
                                eta_expand_with_type env t ty))
                | uu____19324 ->
                    let uu____19325 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___282_19333 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___282_19333.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___282_19333.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___282_19333.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___282_19333.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___282_19333.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___282_19333.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___282_19333.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___282_19333.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___282_19333.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___282_19333.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___282_19333.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___282_19333.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___282_19333.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___282_19333.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___282_19333.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___282_19333.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___282_19333.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___282_19333.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___282_19333.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___282_19333.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___282_19333.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___282_19333.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___282_19333.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___282_19333.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___282_19333.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___282_19333.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___282_19333.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___282_19333.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___282_19333.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___282_19333.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___282_19333.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19325 with
                     | (uu____19334,ty,uu____19336) ->
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
            | (uu____19410,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19416,FStar_Util.Inl t) ->
                let uu____19422 =
                  let uu____19425 =
                    let uu____19426 =
                      let uu____19439 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19439) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19426 in
                  FStar_Syntax_Syntax.mk uu____19425 in
                uu____19422 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19443 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19443 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19470 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19525 ->
                    let uu____19526 =
                      let uu____19535 =
                        let uu____19536 = FStar_Syntax_Subst.compress t3 in
                        uu____19536.FStar_Syntax_Syntax.n in
                      (uu____19535, tc) in
                    (match uu____19526 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19561) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19598) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19637,FStar_Util.Inl uu____19638) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19661 -> failwith "Impossible") in
              (match uu____19470 with
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
          let uu____19766 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19766 with
          | (univ_names1,binders1,tc) ->
              let uu____19824 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19824)
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
          let uu____19859 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19859 with
          | (univ_names1,binders1,tc) ->
              let uu____19919 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19919)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19952 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19952 with
           | (univ_names1,binders1,typ1) ->
               let uu___283_19980 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_19980.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_19980.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_19980.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_19980.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___284_20001 = s in
          let uu____20002 =
            let uu____20003 =
              let uu____20012 = FStar_List.map (elim_uvars env) sigs in
              (uu____20012, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20003 in
          {
            FStar_Syntax_Syntax.sigel = uu____20002;
            FStar_Syntax_Syntax.sigrng =
              (uu___284_20001.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___284_20001.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___284_20001.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___284_20001.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20029 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20029 with
           | (univ_names1,uu____20047,typ1) ->
               let uu___285_20061 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___285_20061.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___285_20061.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___285_20061.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___285_20061.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20067 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20067 with
           | (univ_names1,uu____20085,typ1) ->
               let uu___286_20099 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___286_20099.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___286_20099.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___286_20099.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___286_20099.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20133 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20133 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20156 =
                            let uu____20157 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20157 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20156 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___287_20160 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___287_20160.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___287_20160.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___288_20161 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___288_20161.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___288_20161.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___288_20161.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___288_20161.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___289_20173 = s in
          let uu____20174 =
            let uu____20175 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20175 in
          {
            FStar_Syntax_Syntax.sigel = uu____20174;
            FStar_Syntax_Syntax.sigrng =
              (uu___289_20173.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___289_20173.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___289_20173.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___289_20173.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20179 = elim_uvars_aux_t env us [] t in
          (match uu____20179 with
           | (us1,uu____20197,t1) ->
               let uu___290_20211 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___290_20211.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___290_20211.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___290_20211.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___290_20211.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20212 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20214 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20214 with
           | (univs1,binders,signature) ->
               let uu____20242 =
                 let uu____20251 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20251 with
                 | (univs_opening,univs2) ->
                     let uu____20278 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20278) in
               (match uu____20242 with
                | (univs_opening,univs_closing) ->
                    let uu____20295 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20301 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20302 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20301, uu____20302) in
                    (match uu____20295 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20324 =
                           match uu____20324 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20342 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20342 with
                                | (us1,t1) ->
                                    let uu____20353 =
                                      let uu____20358 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20365 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20358, uu____20365) in
                                    (match uu____20353 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20378 =
                                           let uu____20383 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20392 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20383, uu____20392) in
                                         (match uu____20378 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20408 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20408 in
                                              let uu____20409 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20409 with
                                               | (uu____20430,uu____20431,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20446 =
                                                       let uu____20447 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20447 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20446 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20452 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20452 with
                           | (uu____20465,uu____20466,t1) -> t1 in
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
                             | uu____20526 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20543 =
                               let uu____20544 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20544.FStar_Syntax_Syntax.n in
                             match uu____20543 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20603 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20632 =
                               let uu____20633 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20633.FStar_Syntax_Syntax.n in
                             match uu____20632 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20654) ->
                                 let uu____20675 = destruct_action_body body in
                                 (match uu____20675 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20720 ->
                                 let uu____20721 = destruct_action_body t in
                                 (match uu____20721 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20770 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20770 with
                           | (action_univs,t) ->
                               let uu____20779 = destruct_action_typ_templ t in
                               (match uu____20779 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___291_20820 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___291_20820.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___291_20820.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___292_20822 = ed in
                           let uu____20823 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20824 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20825 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20826 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20827 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20828 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20829 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20830 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20831 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20832 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20833 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20836 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___292_20822.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___292_20822.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20823;
                             FStar_Syntax_Syntax.bind_wp = uu____20824;
                             FStar_Syntax_Syntax.if_then_else = uu____20825;
                             FStar_Syntax_Syntax.ite_wp = uu____20826;
                             FStar_Syntax_Syntax.stronger = uu____20827;
                             FStar_Syntax_Syntax.close_wp = uu____20828;
                             FStar_Syntax_Syntax.assert_p = uu____20829;
                             FStar_Syntax_Syntax.assume_p = uu____20830;
                             FStar_Syntax_Syntax.null_wp = uu____20831;
                             FStar_Syntax_Syntax.trivial = uu____20832;
                             FStar_Syntax_Syntax.repr = uu____20833;
                             FStar_Syntax_Syntax.return_repr = uu____20834;
                             FStar_Syntax_Syntax.bind_repr = uu____20835;
                             FStar_Syntax_Syntax.actions = uu____20836
                           } in
                         let uu___293_20839 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___293_20839.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___293_20839.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___293_20839.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___293_20839.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___204_20856 =
            match uu___204_20856 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20883 = elim_uvars_aux_t env us [] t in
                (match uu____20883 with
                 | (us1,uu____20907,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___294_20926 = sub_eff in
            let uu____20927 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20930 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___294_20926.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___294_20926.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20927;
              FStar_Syntax_Syntax.lift = uu____20930
            } in
          let uu___295_20933 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___295_20933.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___295_20933.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___295_20933.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___295_20933.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20943 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20943 with
           | (univ_names1,binders1,comp1) ->
               let uu___296_20977 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___296_20977.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___296_20977.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___296_20977.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___296_20977.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20988 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t