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
    match projectee with | Clos _0 -> true | uu____369 -> false
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
    match projectee with | Univ _0 -> true | uu____471 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____482 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___71_501  ->
    match uu___71_501 with
    | Clos (uu____502,t,uu____504,uu____505) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____550 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____794 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____830 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____866 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____935 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____977 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1033 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1073 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1105 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1151 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1197 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1222 .
    'Auu____1222 ->
      FStar_Range.range -> 'Auu____1222 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1282 = FStar_ST.op_Bang r in
      match uu____1282 with
      | FStar_Pervasives_Native.Some uu____1359 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1441 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1441 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___72_1448  ->
    match uu___72_1448 with
    | Arg (c,uu____1450,uu____1451) ->
        let uu____1452 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1452
    | MemoLazy uu____1453 -> "MemoLazy"
    | Abs (uu____1460,bs,uu____1462,uu____1463,uu____1464) ->
        let uu____1469 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1469
    | UnivArgs uu____1474 -> "UnivArgs"
    | Match uu____1481 -> "Match"
    | App (uu____1488,t,uu____1490,uu____1491) ->
        let uu____1492 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1492
    | Meta (m,uu____1494) -> "Meta"
    | Let uu____1495 -> "Let"
    | Steps (uu____1504,uu____1505,uu____1506) -> "Steps"
    | Debug (t,uu____1516) ->
        let uu____1517 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1517
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1525 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1525 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1541 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1541 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1554 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1554 then f () else ()
let is_empty: 'Auu____1558 . 'Auu____1558 Prims.list -> Prims.bool =
  fun uu___73_1564  ->
    match uu___73_1564 with | [] -> true | uu____1567 -> false
let lookup_bvar:
  'Auu____1574 'Auu____1575 .
    ('Auu____1575,'Auu____1574) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1574
  =
  fun env  ->
    fun x  ->
      try
        let uu____1599 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1599
      with
      | uu____1612 ->
          let uu____1613 =
            let uu____1614 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1614 in
          failwith uu____1613
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
          let uu____1651 =
            FStar_List.fold_left
              (fun uu____1677  ->
                 fun u1  ->
                   match uu____1677 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1702 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1702 with
                        | (k_u,n1) ->
                            let uu____1717 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1717
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1651 with
          | (uu____1735,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1760 =
                   let uu____1761 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1761 in
                 match uu____1760 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1779 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1788 ->
                   let uu____1789 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1789
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1795 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1804 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1813 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1820 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1820 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1837 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1837 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1845 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1853 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1853 with
                                  | (uu____1858,m) -> n1 <= m)) in
                        if uu____1845 then rest1 else us1
                    | uu____1863 -> us1)
               | uu____1868 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1872 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1872 in
        let uu____1875 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1875
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1877 = aux u in
           match uu____1877 with
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
          (fun uu____1981  ->
             let uu____1982 = FStar_Syntax_Print.tag_of_term t in
             let uu____1983 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1982
               uu____1983);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1990 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1992 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2017 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2018 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2019 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2020 ->
                  let uu____2037 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2037
                  then
                    let uu____2038 =
                      let uu____2039 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2040 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2039 uu____2040 in
                    failwith uu____2038
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2043 =
                    let uu____2044 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2044 in
                  mk uu____2043 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2051 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2051
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2053 = lookup_bvar env x in
                  (match uu____2053 with
                   | Univ uu____2056 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2060) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2172 = closures_as_binders_delayed cfg env bs in
                  (match uu____2172 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2200 =
                         let uu____2201 =
                           let uu____2218 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2218) in
                         FStar_Syntax_Syntax.Tm_abs uu____2201 in
                       mk uu____2200 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2249 = closures_as_binders_delayed cfg env bs in
                  (match uu____2249 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2291 =
                    let uu____2302 =
                      let uu____2309 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2309] in
                    closures_as_binders_delayed cfg env uu____2302 in
                  (match uu____2291 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2327 =
                         let uu____2328 =
                           let uu____2335 =
                             let uu____2336 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2336
                               FStar_Pervasives_Native.fst in
                           (uu____2335, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2328 in
                       mk uu____2327 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2427 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2427
                    | FStar_Util.Inr c ->
                        let uu____2441 = close_comp cfg env c in
                        FStar_Util.Inr uu____2441 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2457 =
                    let uu____2458 =
                      let uu____2485 = closure_as_term_delayed cfg env t11 in
                      (uu____2485, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2458 in
                  mk uu____2457 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2536 =
                    let uu____2537 =
                      let uu____2544 = closure_as_term_delayed cfg env t' in
                      let uu____2547 =
                        let uu____2548 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2548 in
                      (uu____2544, uu____2547) in
                    FStar_Syntax_Syntax.Tm_meta uu____2537 in
                  mk uu____2536 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2608 =
                    let uu____2609 =
                      let uu____2616 = closure_as_term_delayed cfg env t' in
                      let uu____2619 =
                        let uu____2620 =
                          let uu____2627 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2627) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2620 in
                      (uu____2616, uu____2619) in
                    FStar_Syntax_Syntax.Tm_meta uu____2609 in
                  mk uu____2608 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2646 =
                    let uu____2647 =
                      let uu____2654 = closure_as_term_delayed cfg env t' in
                      let uu____2657 =
                        let uu____2658 =
                          let uu____2667 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2667) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2658 in
                      (uu____2654, uu____2657) in
                    FStar_Syntax_Syntax.Tm_meta uu____2647 in
                  mk uu____2646 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2680 =
                    let uu____2681 =
                      let uu____2688 = closure_as_term_delayed cfg env t' in
                      (uu____2688, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2681 in
                  mk uu____2680 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2728  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2747 =
                    let uu____2758 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2758
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2777 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___92_2789 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___92_2789.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___92_2789.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2777)) in
                  (match uu____2747 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___93_2805 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___93_2805.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___93_2805.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2816,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2875  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2900 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2900
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2920  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2942 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2942
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___94_2954 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___94_2954.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___94_2954.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___95_2955 = lb in
                    let uu____2956 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___95_2955.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___95_2955.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2956
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2986  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3075 =
                    match uu____3075 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3130 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3151 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3211  ->
                                        fun uu____3212  ->
                                          match (uu____3211, uu____3212) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3303 =
                                                norm_pat env3 p1 in
                                              (match uu____3303 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3151 with
                               | (pats1,env3) ->
                                   ((let uu___96_3385 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___96_3385.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___97_3404 = x in
                                let uu____3405 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___97_3404.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___97_3404.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3405
                                } in
                              ((let uu___98_3419 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___98_3419.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___99_3430 = x in
                                let uu____3431 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___99_3430.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___99_3430.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3431
                                } in
                              ((let uu___100_3445 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___100_3445.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___101_3461 = x in
                                let uu____3462 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___101_3461.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___101_3461.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3462
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___102_3469 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___102_3469.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3472 = norm_pat env1 pat in
                        (match uu____3472 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3501 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3501 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3507 =
                    let uu____3508 =
                      let uu____3531 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3531) in
                    FStar_Syntax_Syntax.Tm_match uu____3508 in
                  mk uu____3507 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3617 -> closure_as_term cfg env t
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
        | uu____3643 ->
            FStar_List.map
              (fun uu____3660  ->
                 match uu____3660 with
                 | (x,imp) ->
                     let uu____3679 = closure_as_term_delayed cfg env x in
                     (uu____3679, imp)) args
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
        let uu____3693 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3742  ->
                  fun uu____3743  ->
                    match (uu____3742, uu____3743) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___103_3813 = b in
                          let uu____3814 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___103_3813.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___103_3813.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3814
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3693 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3907 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3920 = closure_as_term_delayed cfg env t in
                 let uu____3921 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3920 uu____3921
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3934 = closure_as_term_delayed cfg env t in
                 let uu____3935 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3934 uu____3935
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
                        (fun uu___74_3961  ->
                           match uu___74_3961 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3965 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3965
                           | f -> f)) in
                 let uu____3969 =
                   let uu___104_3970 = c1 in
                   let uu____3971 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3971;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___104_3970.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3969)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___75_3981  ->
            match uu___75_3981 with
            | FStar_Syntax_Syntax.DECREASES uu____3982 -> false
            | uu____3985 -> true))
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
                   (fun uu___76_4003  ->
                      match uu___76_4003 with
                      | FStar_Syntax_Syntax.DECREASES uu____4004 -> false
                      | uu____4007 -> true)) in
            let rc1 =
              let uu___105_4009 = rc in
              let uu____4010 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___105_4009.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4010;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4017 -> lopt
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
    let uu____4107 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4107 in
  let arg_as_bounded_int uu____4135 =
    match uu____4135 with
    | (a,uu____4147) ->
        let uu____4154 =
          let uu____4155 = FStar_Syntax_Subst.compress a in
          uu____4155.FStar_Syntax_Syntax.n in
        (match uu____4154 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4165;
                FStar_Syntax_Syntax.vars = uu____4166;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4168;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4169;_},uu____4170)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4209 =
               let uu____4214 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4214) in
             FStar_Pervasives_Native.Some uu____4209
         | uu____4219 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4261 = f a in FStar_Pervasives_Native.Some uu____4261
    | uu____4262 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4312 = f a0 a1 in FStar_Pervasives_Native.Some uu____4312
    | uu____4313 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4362 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4362 in
  let binary_op as_a f res args =
    let uu____4418 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4418 in
  let as_primitive_step uu____4442 =
    match uu____4442 with
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
           let uu____4490 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4490) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4518 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4518) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4539 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4539) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4567 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4567) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4595 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4595) in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4712 =
          let uu____4721 = as_a a in
          let uu____4724 = as_b b in (uu____4721, uu____4724) in
        (match uu____4712 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4739 =
               let uu____4740 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4740 in
             FStar_Pervasives_Native.Some uu____4739
         | uu____4741 -> FStar_Pervasives_Native.None)
    | uu____4750 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4764 =
        let uu____4765 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4765 in
      mk uu____4764 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4775 =
      let uu____4778 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4778 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4775 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4810 =
      let uu____4811 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4811 in
    FStar_Syntax_Embeddings.embed_int rng uu____4810 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4829 = arg_as_string a1 in
        (match uu____4829 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4835 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4835 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4848 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4848
              | uu____4849 -> FStar_Pervasives_Native.None)
         | uu____4854 -> FStar_Pervasives_Native.None)
    | uu____4857 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4867 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4867 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4891 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4902 =
          let uu____4923 = arg_as_string fn in
          let uu____4926 = arg_as_int from_line in
          let uu____4929 = arg_as_int from_col in
          let uu____4932 = arg_as_int to_line in
          let uu____4935 = arg_as_int to_col in
          (uu____4923, uu____4926, uu____4929, uu____4932, uu____4935) in
        (match uu____4902 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4966 =
                 let uu____4967 = FStar_BigInt.to_int_fs from_l in
                 let uu____4968 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4967 uu____4968 in
               let uu____4969 =
                 let uu____4970 = FStar_BigInt.to_int_fs to_l in
                 let uu____4971 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4970 uu____4971 in
               FStar_Range.mk_range fn1 uu____4966 uu____4969 in
             let uu____4972 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4972
         | uu____4977 -> FStar_Pervasives_Native.None)
    | uu____4998 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5025)::(a1,uu____5027)::(a2,uu____5029)::[] ->
        let uu____5066 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5066 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5079 -> FStar_Pervasives_Native.None)
    | uu____5080 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5107)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5116 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5140 =
      let uu____5155 =
        let uu____5170 =
          let uu____5185 =
            let uu____5200 =
              let uu____5215 =
                let uu____5230 =
                  let uu____5245 =
                    let uu____5260 =
                      let uu____5275 =
                        let uu____5290 =
                          let uu____5305 =
                            let uu____5320 =
                              let uu____5335 =
                                let uu____5350 =
                                  let uu____5365 =
                                    let uu____5380 =
                                      let uu____5395 =
                                        let uu____5410 =
                                          let uu____5425 =
                                            let uu____5440 =
                                              let uu____5453 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5453,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5460 =
                                              let uu____5475 =
                                                let uu____5488 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5488,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5499 =
                                                let uu____5514 =
                                                  let uu____5529 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5529,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5538 =
                                                  let uu____5555 =
                                                    let uu____5570 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5570,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5579 =
                                                    let uu____5596 =
                                                      let uu____5615 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5615,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5596] in
                                                  uu____5555 :: uu____5579 in
                                                uu____5514 :: uu____5538 in
                                              uu____5475 :: uu____5499 in
                                            uu____5440 :: uu____5460 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5425 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5410 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5395 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5380 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5365 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5833 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5833 y)))
                                  :: uu____5350 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5335 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5320 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5305 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5290 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5275 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5979 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5979)))
                      :: uu____5260 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____6005 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____6005)))
                    :: uu____5245 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____6031 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____6031)))
                  :: uu____5230 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____6057 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____6057)))
                :: uu____5215 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5200 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5185 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5170 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5155 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5140 in
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
      let uu____6207 =
        let uu____6208 =
          let uu____6209 = FStar_Syntax_Syntax.as_arg c in [uu____6209] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6208 in
      uu____6207 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6244 =
              let uu____6257 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6257, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6277  ->
                        fun uu____6278  ->
                          match (uu____6277, uu____6278) with
                          | ((int_to_t1,x),(uu____6297,y)) ->
                              let uu____6307 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6307))) in
            let uu____6308 =
              let uu____6323 =
                let uu____6336 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6336, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6356  ->
                          fun uu____6357  ->
                            match (uu____6356, uu____6357) with
                            | ((int_to_t1,x),(uu____6376,y)) ->
                                let uu____6386 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6386))) in
              let uu____6387 =
                let uu____6402 =
                  let uu____6415 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6415, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6435  ->
                            fun uu____6436  ->
                              match (uu____6435, uu____6436) with
                              | ((int_to_t1,x),(uu____6455,y)) ->
                                  let uu____6465 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6465))) in
                [uu____6402] in
              uu____6323 :: uu____6387 in
            uu____6244 :: uu____6308)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6555)::(a1,uu____6557)::(a2,uu____6559)::[] ->
        let uu____6596 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6596 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6602 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6602.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6602.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6606 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6606.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6606.FStar_Syntax_Syntax.vars)
                })
         | uu____6607 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6609)::uu____6610::(a1,uu____6612)::(a2,uu____6614)::[] ->
        let uu____6663 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6663 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6669 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6669.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6669.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6673 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6673.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6673.FStar_Syntax_Syntax.vars)
                })
         | uu____6674 -> FStar_Pervasives_Native.None)
    | uu____6675 -> failwith "Unexpected number of arguments" in
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
      let uu____6694 =
        let uu____6695 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6695 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6694
    with | uu____6701 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6705 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6705) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6765  ->
           fun subst1  ->
             match uu____6765 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6807)) ->
                      let uu____6866 = b in
                      (match uu____6866 with
                       | (bv,uu____6874) ->
                           let uu____6875 =
                             let uu____6876 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6876 in
                           if uu____6875
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6881 = unembed_binder term1 in
                              match uu____6881 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6888 =
                                      let uu___110_6889 = bv in
                                      let uu____6890 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___110_6889.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___110_6889.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6890
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6888 in
                                  let b_for_x =
                                    let uu____6894 =
                                      let uu____6901 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6901) in
                                    FStar_Syntax_Syntax.NT uu____6894 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___77_6910  ->
                                         match uu___77_6910 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6911,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6913;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6914;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6919 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6920 -> subst1)) env []
let reduce_primops:
  'Auu____6937 'Auu____6938 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6938) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6937 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6979 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6979
          then tm
          else
            (let uu____6981 = FStar_Syntax_Util.head_and_args tm in
             match uu____6981 with
             | (head1,args) ->
                 let uu____7018 =
                   let uu____7019 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7019.FStar_Syntax_Syntax.n in
                 (match uu____7018 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7023 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7023 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7040  ->
                                   let uu____7041 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7042 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7049 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7041 uu____7042 uu____7049);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7054  ->
                                   let uu____7055 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7055);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7058  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7060 =
                                 prim_step.interpretation psc args in
                               match uu____7060 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7066  ->
                                         let uu____7067 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7067);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7073  ->
                                         let uu____7074 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7075 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7074 uu____7075);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7076 ->
                           (log_primops cfg
                              (fun uu____7080  ->
                                 let uu____7081 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7081);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7085  ->
                            let uu____7086 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7086);
                       (match args with
                        | (a1,uu____7088)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7105 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7117  ->
                            let uu____7118 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7118);
                       (match args with
                        | (a1,uu____7120)::(a2,uu____7122)::[] ->
                            let uu____7149 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____7149 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___111_7153 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___111_7153.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___111_7153.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7156 -> tm))
                  | uu____7165 -> tm))
let reduce_equality:
  'Auu____7170 'Auu____7171 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7171) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7170 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___112_7209 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___112_7209.tcenv);
           delta_level = (uu___112_7209.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___112_7209.strong)
         }) tm
let maybe_simplify_aux:
  'Auu____7216 'Auu____7217 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7217) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7216 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7259 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7259
          then tm1
          else
            (let w t =
               let uu___113_7271 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___113_7271.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___113_7271.FStar_Syntax_Syntax.vars)
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
               | uu____7288 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7293 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7293
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7314 =
                 match uu____7314 with
                 | (t1,q) ->
                     let uu____7327 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7327 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7355 -> (t1, q)) in
               let uu____7364 = FStar_Syntax_Util.head_and_args t in
               match uu____7364 with
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
                         FStar_Syntax_Syntax.pos = uu____7461;
                         FStar_Syntax_Syntax.vars = uu____7462;_},uu____7463);
                    FStar_Syntax_Syntax.pos = uu____7464;
                    FStar_Syntax_Syntax.vars = uu____7465;_},args)
                 ->
                 let uu____7491 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7491
                 then
                   let uu____7492 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7492 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7547)::
                        (uu____7548,(arg,uu____7550))::[] ->
                        maybe_auto_squash arg
                    | (uu____7615,(arg,uu____7617))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7618)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7683)::uu____7684::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7747::(FStar_Pervasives_Native.Some (false
                                   ),uu____7748)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7811 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7827 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7827
                    then
                      let uu____7828 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7828 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7883)::uu____7884::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7947::(FStar_Pervasives_Native.Some (true
                                     ),uu____7948)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8011)::
                          (uu____8012,(arg,uu____8014))::[] ->
                          maybe_auto_squash arg
                      | (uu____8079,(arg,uu____8081))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8082)::[]
                          -> maybe_auto_squash arg
                      | uu____8147 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8163 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8163
                       then
                         let uu____8164 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8164 with
                         | uu____8219::(FStar_Pervasives_Native.Some (true
                                        ),uu____8220)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8283)::uu____8284::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8347)::
                             (uu____8348,(arg,uu____8350))::[] ->
                             maybe_auto_squash arg
                         | (uu____8415,(p,uu____8417))::(uu____8418,(q,uu____8420))::[]
                             ->
                             let uu____8485 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8485
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8487 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8503 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8503
                          then
                            let uu____8504 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8504 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8559)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8598)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8637 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8653 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8653
                             then
                               match args with
                               | (t,uu____8655)::[] ->
                                   let uu____8672 =
                                     let uu____8673 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8673.FStar_Syntax_Syntax.n in
                                   (match uu____8672 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8676::[],body,uu____8678) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8705 -> tm1)
                                    | uu____8708 -> tm1)
                               | (uu____8709,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8710))::
                                   (t,uu____8712)::[] ->
                                   let uu____8751 =
                                     let uu____8752 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8752.FStar_Syntax_Syntax.n in
                                   (match uu____8751 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8755::[],body,uu____8757) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8784 -> tm1)
                                    | uu____8787 -> tm1)
                               | uu____8788 -> tm1
                             else
                               (let uu____8798 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8798
                                then
                                  match args with
                                  | (t,uu____8800)::[] ->
                                      let uu____8817 =
                                        let uu____8818 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8818.FStar_Syntax_Syntax.n in
                                      (match uu____8817 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8821::[],body,uu____8823)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8850 -> tm1)
                                       | uu____8853 -> tm1)
                                  | (uu____8854,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8855))::(t,uu____8857)::[] ->
                                      let uu____8896 =
                                        let uu____8897 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8897.FStar_Syntax_Syntax.n in
                                      (match uu____8896 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8900::[],body,uu____8902)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8929 -> tm1)
                                       | uu____8932 -> tm1)
                                  | uu____8933 -> tm1
                                else
                                  (let uu____8943 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8943
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8944;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8945;_},uu____8946)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8963;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8964;_},uu____8965)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8982 -> tm1
                                   else
                                     (let uu____8992 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8992 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9012 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9022;
                    FStar_Syntax_Syntax.vars = uu____9023;_},args)
                 ->
                 let uu____9045 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9045
                 then
                   let uu____9046 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9046 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9101)::
                        (uu____9102,(arg,uu____9104))::[] ->
                        maybe_auto_squash arg
                    | (uu____9169,(arg,uu____9171))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9172)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9237)::uu____9238::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9301::(FStar_Pervasives_Native.Some (false
                                   ),uu____9302)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9365 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9381 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9381
                    then
                      let uu____9382 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9382 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9437)::uu____9438::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9501::(FStar_Pervasives_Native.Some (true
                                     ),uu____9502)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9565)::
                          (uu____9566,(arg,uu____9568))::[] ->
                          maybe_auto_squash arg
                      | (uu____9633,(arg,uu____9635))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9636)::[]
                          -> maybe_auto_squash arg
                      | uu____9701 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9717 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9717
                       then
                         let uu____9718 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9718 with
                         | uu____9773::(FStar_Pervasives_Native.Some (true
                                        ),uu____9774)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9837)::uu____9838::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9901)::
                             (uu____9902,(arg,uu____9904))::[] ->
                             maybe_auto_squash arg
                         | (uu____9969,(p,uu____9971))::(uu____9972,(q,uu____9974))::[]
                             ->
                             let uu____10039 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10039
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10041 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10057 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10057
                          then
                            let uu____10058 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10058 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10113)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10152)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10191 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10207 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10207
                             then
                               match args with
                               | (t,uu____10209)::[] ->
                                   let uu____10226 =
                                     let uu____10227 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10227.FStar_Syntax_Syntax.n in
                                   (match uu____10226 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10230::[],body,uu____10232) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10259 -> tm1)
                                    | uu____10262 -> tm1)
                               | (uu____10263,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10264))::
                                   (t,uu____10266)::[] ->
                                   let uu____10305 =
                                     let uu____10306 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10306.FStar_Syntax_Syntax.n in
                                   (match uu____10305 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10309::[],body,uu____10311) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10338 -> tm1)
                                    | uu____10341 -> tm1)
                               | uu____10342 -> tm1
                             else
                               (let uu____10352 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10352
                                then
                                  match args with
                                  | (t,uu____10354)::[] ->
                                      let uu____10371 =
                                        let uu____10372 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10372.FStar_Syntax_Syntax.n in
                                      (match uu____10371 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10375::[],body,uu____10377)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10404 -> tm1)
                                       | uu____10407 -> tm1)
                                  | (uu____10408,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10409))::(t,uu____10411)::[] ->
                                      let uu____10450 =
                                        let uu____10451 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10451.FStar_Syntax_Syntax.n in
                                      (match uu____10450 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10454::[],body,uu____10456)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10483 -> tm1)
                                       | uu____10486 -> tm1)
                                  | uu____10487 -> tm1
                                else
                                  (let uu____10497 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10497
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10498;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10499;_},uu____10500)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10517;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10518;_},uu____10519)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10536 -> tm1
                                   else
                                     (let uu____10546 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10546 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10566 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10575 -> tm1)
let maybe_simplify:
  'Auu____10582 'Auu____10583 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10583) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10582 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10626 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10626
           then
             let uu____10627 = FStar_Syntax_Print.term_to_string tm in
             let uu____10628 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10627 uu____10628
           else ());
          tm'
let is_norm_request:
  'Auu____10634 .
    FStar_Syntax_Syntax.term -> 'Auu____10634 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10647 =
        let uu____10654 =
          let uu____10655 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10655.FStar_Syntax_Syntax.n in
        (uu____10654, args) in
      match uu____10647 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10661::uu____10662::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10666::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10671::uu____10672::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10675 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___78_10686  ->
    match uu___78_10686 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10692 =
          let uu____10695 =
            let uu____10696 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10696 in
          [uu____10695] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10692
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10711 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10711) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10749 =
          let uu____10752 =
            let uu____10757 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10757 s in
          FStar_All.pipe_right uu____10752 FStar_Util.must in
        FStar_All.pipe_right uu____10749 tr_norm_steps in
      match args with
      | uu____10782::(tm,uu____10784)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10807)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10822)::uu____10823::(tm,uu____10825)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10865 =
              let uu____10868 = full_norm steps in parse_steps uu____10868 in
            Beta :: uu____10865 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10877 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___79_10894  ->
    match uu___79_10894 with
    | (App
        (uu____10897,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10898;
                       FStar_Syntax_Syntax.vars = uu____10899;_},uu____10900,uu____10901))::uu____10902
        -> true
    | uu____10909 -> false
let firstn:
  'Auu____10915 .
    Prims.int ->
      'Auu____10915 Prims.list ->
        ('Auu____10915 Prims.list,'Auu____10915 Prims.list)
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
          (uu____10951,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10952;
                         FStar_Syntax_Syntax.vars = uu____10953;_},uu____10954,uu____10955))::uu____10956
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10963 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11079  ->
               let uu____11080 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11081 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11082 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11089 =
                 let uu____11090 =
                   let uu____11093 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11093 in
                 stack_to_string uu____11090 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11080 uu____11081 uu____11082 uu____11089);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11116 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11141 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11158 =
                 let uu____11159 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11160 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11159 uu____11160 in
               failwith uu____11158
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11161 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11178 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11179 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11180;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11181;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11184;
                 FStar_Syntax_Syntax.fv_delta = uu____11185;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11186;
                 FStar_Syntax_Syntax.fv_delta = uu____11187;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11188);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11196 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11196 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11202  ->
                     let uu____11203 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11204 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11203 uu____11204);
                if b
                then
                  (let uu____11205 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11205 t1 fv)
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
                 let uu___114_11244 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___114_11244.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_11244.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11277 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11277) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___115_11285 = cfg in
                 let uu____11286 =
                   FStar_List.filter
                     (fun uu___80_11289  ->
                        match uu___80_11289 with
                        | UnfoldOnly uu____11290 -> false
                        | NoDeltaSteps  -> false
                        | uu____11293 -> true) cfg.steps in
                 {
                   steps = uu____11286;
                   tcenv = (uu___115_11285.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___115_11285.primitive_steps);
                   strong = (uu___115_11285.strong)
                 } in
               let uu____11294 = get_norm_request (norm cfg' env []) args in
               (match uu____11294 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11310 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___81_11315  ->
                                match uu___81_11315 with
                                | UnfoldUntil uu____11316 -> true
                                | UnfoldOnly uu____11317 -> true
                                | uu____11320 -> false)) in
                      if uu____11310
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___116_11325 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___116_11325.tcenv);
                        delta_level;
                        primitive_steps = (uu___116_11325.primitive_steps);
                        strong = (uu___116_11325.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let uu____11336 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11336
                      then
                        let uu____11339 =
                          let uu____11340 =
                            let uu____11345 = FStar_Util.now () in
                            (t1, uu____11345) in
                          Debug uu____11340 in
                        uu____11339 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11347;
                  FStar_Syntax_Syntax.vars = uu____11348;_},a1::a2::rest)
               ->
               let uu____11396 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11396 with
                | (hd1,uu____11412) ->
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
                  FStar_Syntax_Syntax.pos = uu____11477;
                  FStar_Syntax_Syntax.vars = uu____11478;_},a1::a2::rest)
               ->
               let uu____11526 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11526 with
                | (hd1,uu____11542) ->
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
                  FStar_Syntax_Syntax.pos = uu____11607;
                  FStar_Syntax_Syntax.vars = uu____11608;_},a1::a2::a3::rest)
               ->
               let uu____11669 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11669 with
                | (hd1,uu____11685) ->
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
                    (FStar_Const.Const_reflect uu____11756);
                  FStar_Syntax_Syntax.pos = uu____11757;
                  FStar_Syntax_Syntax.vars = uu____11758;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11790 = FStar_List.tl stack in
               norm cfg env uu____11790 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11793;
                  FStar_Syntax_Syntax.vars = uu____11794;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11826 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11826 with
                | (reify_head,uu____11842) ->
                    let a1 =
                      let uu____11864 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11864 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11867);
                            FStar_Syntax_Syntax.pos = uu____11868;
                            FStar_Syntax_Syntax.vars = uu____11869;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11903 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11913 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11913
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11920 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11920
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11923 =
                      let uu____11930 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11930, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11923 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___82_11943  ->
                         match uu___82_11943 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11946 =
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
                 if uu____11946
                 then false
                 else
                   (let uu____11948 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___83_11955  ->
                              match uu___83_11955 with
                              | UnfoldOnly uu____11956 -> true
                              | uu____11959 -> false)) in
                    match uu____11948 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11963 -> should_delta) in
               (log cfg
                  (fun uu____11971  ->
                     let uu____11972 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11973 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11974 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11972 uu____11973 uu____11974);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11977 = lookup_bvar env x in
               (match uu____11977 with
                | Univ uu____11980 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____12029 = FStar_ST.op_Bang r in
                      (match uu____12029 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12176  ->
                                 let uu____12177 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12178 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12177
                                   uu____12178);
                            (let uu____12179 =
                               let uu____12180 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12180.FStar_Syntax_Syntax.n in
                             match uu____12179 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12183 ->
                                 norm cfg env2 stack t'
                             | uu____12200 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12270)::uu____12271 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12280)::uu____12281 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12291,uu____12292))::stack_rest ->
                    (match c with
                     | Univ uu____12296 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12305 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12326  ->
                                    let uu____12327 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12327);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12367  ->
                                    let uu____12368 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12368);
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
                      (let uu___117_12418 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___117_12418.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___117_12418.strong)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12459  ->
                          let uu____12460 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12460);
                     norm cfg env stack1 t1)
                | (Debug uu____12461)::uu____12462 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12469 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12469
                    else
                      (let uu____12471 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12471 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12513  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12541 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12541
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12551 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12551)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12556 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12556.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12556.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12557 -> lopt in
                           (log cfg
                              (fun uu____12563  ->
                                 let uu____12564 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12564);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12577 = cfg in
                               {
                                 steps = (uu___119_12577.steps);
                                 tcenv = (uu___119_12577.tcenv);
                                 delta_level = (uu___119_12577.delta_level);
                                 primitive_steps =
                                   (uu___119_12577.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12588)::uu____12589 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12596 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12596
                    else
                      (let uu____12598 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12598 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12640  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12668 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12668
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12678 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12678)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12683 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12683.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12683.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12684 -> lopt in
                           (log cfg
                              (fun uu____12690  ->
                                 let uu____12691 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12691);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12704 = cfg in
                               {
                                 steps = (uu___119_12704.steps);
                                 tcenv = (uu___119_12704.tcenv);
                                 delta_level = (uu___119_12704.delta_level);
                                 primitive_steps =
                                   (uu___119_12704.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12715)::uu____12716 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12727 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12727
                    else
                      (let uu____12729 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12729 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12771  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12799 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12799
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12809 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12809)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12814 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12814.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12814.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12815 -> lopt in
                           (log cfg
                              (fun uu____12821  ->
                                 let uu____12822 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12822);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12835 = cfg in
                               {
                                 steps = (uu___119_12835.steps);
                                 tcenv = (uu___119_12835.tcenv);
                                 delta_level = (uu___119_12835.delta_level);
                                 primitive_steps =
                                   (uu___119_12835.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12846)::uu____12847 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12858 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12858
                    else
                      (let uu____12860 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12860 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12902  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12930 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12930
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12940 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12940)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12945 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12945.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12945.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12946 -> lopt in
                           (log cfg
                              (fun uu____12952  ->
                                 let uu____12953 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12953);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_12966 = cfg in
                               {
                                 steps = (uu___119_12966.steps);
                                 tcenv = (uu___119_12966.tcenv);
                                 delta_level = (uu___119_12966.delta_level);
                                 primitive_steps =
                                   (uu___119_12966.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12977)::uu____12978 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12993 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12993
                    else
                      (let uu____12995 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12995 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13037  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13065 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13065
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13075 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13075)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_13080 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_13080.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_13080.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13081 -> lopt in
                           (log cfg
                              (fun uu____13087  ->
                                 let uu____13088 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13088);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_13101 = cfg in
                               {
                                 steps = (uu___119_13101.steps);
                                 tcenv = (uu___119_13101.tcenv);
                                 delta_level = (uu___119_13101.delta_level);
                                 primitive_steps =
                                   (uu___119_13101.primitive_steps);
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
                      let uu____13112 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13112
                    else
                      (let uu____13114 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13114 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13156  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13184 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13184
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13194 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13194)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_13199 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_13199.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_13199.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13200 -> lopt in
                           (log cfg
                              (fun uu____13206  ->
                                 let uu____13207 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13207);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack in
                             let cfg1 =
                               let uu___119_13220 = cfg in
                               {
                                 steps = (uu___119_13220.steps);
                                 tcenv = (uu___119_13220.tcenv);
                                 delta_level = (uu___119_13220.delta_level);
                                 primitive_steps =
                                   (uu___119_13220.primitive_steps);
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
                      (fun uu____13269  ->
                         fun stack1  ->
                           match uu____13269 with
                           | (a,aq) ->
                               let uu____13281 =
                                 let uu____13282 =
                                   let uu____13289 =
                                     let uu____13290 =
                                       let uu____13321 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13321, false) in
                                     Clos uu____13290 in
                                   (uu____13289, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13282 in
                               uu____13281 :: stack1) args) in
               (log cfg
                  (fun uu____13405  ->
                     let uu____13406 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13406);
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
                             ((let uu___120_13442 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_13442.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_13442.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13443 ->
                      let uu____13448 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13448)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13451 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13451 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13482 =
                          let uu____13483 =
                            let uu____13490 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_13492 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_13492.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_13492.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13490) in
                          FStar_Syntax_Syntax.Tm_refine uu____13483 in
                        mk uu____13482 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13511 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13511
               else
                 (let uu____13513 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13513 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13521 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13545  -> dummy :: env1) env) in
                        norm_comp cfg uu____13521 c1 in
                      let t2 =
                        let uu____13567 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13567 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13626)::uu____13627 ->
                    (log cfg
                       (fun uu____13638  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13639)::uu____13640 ->
                    (log cfg
                       (fun uu____13651  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13652,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13653;
                                   FStar_Syntax_Syntax.vars = uu____13654;_},uu____13655,uu____13656))::uu____13657
                    ->
                    (log cfg
                       (fun uu____13666  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13667)::uu____13668 ->
                    (log cfg
                       (fun uu____13679  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13680 ->
                    (log cfg
                       (fun uu____13683  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13687  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13704 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13704
                         | FStar_Util.Inr c ->
                             let uu____13712 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13712 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Steps (s,ps,dl))::stack1 ->
                           let t2 =
                             let uu____13735 =
                               let uu____13736 =
                                 let uu____13763 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13763, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13736 in
                             mk uu____13735 t1.FStar_Syntax_Syntax.pos in
                           norm
                             (let uu___122_13784 = cfg in
                              {
                                steps = s;
                                tcenv = (uu___122_13784.tcenv);
                                delta_level = dl;
                                primitive_steps = ps;
                                strong = (uu___122_13784.strong)
                              }) env stack1 t2
                       | uu____13785 ->
                           let uu____13786 =
                             let uu____13787 =
                               let uu____13788 =
                                 let uu____13815 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13815, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13788 in
                             mk uu____13787 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13786))))
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
                         let uu____13925 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13925 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___123_13945 = cfg in
                               let uu____13946 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___123_13945.steps);
                                 tcenv = uu____13946;
                                 delta_level = (uu___123_13945.delta_level);
                                 primitive_steps =
                                   (uu___123_13945.primitive_steps);
                                 strong = (uu___123_13945.strong)
                               } in
                             let norm1 t2 =
                               let uu____13951 =
                                 let uu____13952 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13952 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13951 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___124_13955 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___124_13955.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___124_13955.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13956 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13956
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13967,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13968;
                               FStar_Syntax_Syntax.lbunivs = uu____13969;
                               FStar_Syntax_Syntax.lbtyp = uu____13970;
                               FStar_Syntax_Syntax.lbeff = uu____13971;
                               FStar_Syntax_Syntax.lbdef = uu____13972;_}::uu____13973),uu____13974)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____14010 =
                 (let uu____14013 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____14013) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____14015 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____14015))) in
               if uu____14010
               then
                 let binder =
                   let uu____14017 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____14017 in
                 let env1 =
                   let uu____14027 =
                     let uu____14034 =
                       let uu____14035 =
                         let uu____14066 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14066,
                           false) in
                       Clos uu____14035 in
                     ((FStar_Pervasives_Native.Some binder), uu____14034) in
                   uu____14027 :: env in
                 (log cfg
                    (fun uu____14159  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____14161 =
                    let uu____14166 =
                      let uu____14167 =
                        let uu____14168 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14168
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14167] in
                    FStar_Syntax_Subst.open_term uu____14166 body in
                  match uu____14161 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____14177  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____14185 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____14185 in
                          FStar_Util.Inl
                            (let uu___125_14195 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___125_14195.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___125_14195.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____14198  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___126_14200 = lb in
                           let uu____14201 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___126_14200.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___126_14200.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____14201
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____14236  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___127_14256 = cfg in
                           {
                             steps = (uu___127_14256.steps);
                             tcenv = (uu___127_14256.tcenv);
                             delta_level = (uu___127_14256.delta_level);
                             primitive_steps =
                               (uu___127_14256.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____14259  ->
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
               let uu____14276 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14276 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14312 =
                               let uu___128_14313 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___128_14313.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___128_14313.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14312 in
                           let uu____14314 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14314 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14340 =
                                   FStar_List.map (fun uu____14356  -> dummy)
                                     lbs1 in
                                 let uu____14357 =
                                   let uu____14366 =
                                     FStar_List.map
                                       (fun uu____14386  -> dummy) xs1 in
                                   FStar_List.append uu____14366 env in
                                 FStar_List.append uu____14340 uu____14357 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14410 =
                                       let uu___129_14411 = rc in
                                       let uu____14412 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___129_14411.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14412;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___129_14411.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14410
                                 | uu____14419 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___130_14423 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___130_14423.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___130_14423.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14433 =
                        FStar_List.map (fun uu____14449  -> dummy) lbs2 in
                      FStar_List.append uu____14433 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14457 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14457 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___131_14473 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___131_14473.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___131_14473.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14500 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14500
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14519 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14595  ->
                        match uu____14595 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___132_14716 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___132_14716.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___132_14716.FStar_Syntax_Syntax.sort)
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
               (match uu____14519 with
                | (rec_env,memos,uu____14929) ->
                    let uu____14982 =
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
                             let uu____15525 =
                               let uu____15532 =
                                 let uu____15533 =
                                   let uu____15564 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15564, false) in
                                 Clos uu____15533 in
                               (FStar_Pervasives_Native.None, uu____15532) in
                             uu____15525 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15677 =
                      let uu____15678 = should_reify cfg stack in
                      Prims.op_Negation uu____15678 in
                    if uu____15677
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack in
                      let cfg1 =
                        let uu____15688 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15688
                        then
                          let uu___133_15689 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___133_15689.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___133_15689.primitive_steps);
                            strong = (uu___133_15689.strong)
                          }
                        else
                          (let uu___134_15691 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___134_15691.tcenv);
                             delta_level = (uu___134_15691.delta_level);
                             primitive_steps =
                               (uu___134_15691.primitive_steps);
                             strong = (uu___134_15691.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15693 =
                         let uu____15694 = FStar_Syntax_Subst.compress head1 in
                         uu____15694.FStar_Syntax_Syntax.n in
                       match uu____15693 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15712 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15712 with
                            | (uu____15713,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15719 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15727 =
                                         let uu____15728 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15728.FStar_Syntax_Syntax.n in
                                       match uu____15727 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15734,uu____15735))
                                           ->
                                           let uu____15744 =
                                             let uu____15745 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15745.FStar_Syntax_Syntax.n in
                                           (match uu____15744 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15751,msrc,uu____15753))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15762 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15762
                                            | uu____15763 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15764 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15765 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15765 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___135_15770 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___135_15770.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___135_15770.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___135_15770.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15771 =
                                            FStar_List.tl stack in
                                          let uu____15772 =
                                            let uu____15773 =
                                              let uu____15776 =
                                                let uu____15777 =
                                                  let uu____15790 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15790) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15777 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15776 in
                                            uu____15773
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15771
                                            uu____15772
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15806 =
                                            let uu____15807 = is_return body in
                                            match uu____15807 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15811;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15812;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15817 -> false in
                                          if uu____15806
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
                                               let uu____15841 =
                                                 let uu____15844 =
                                                   let uu____15845 =
                                                     let uu____15862 =
                                                       let uu____15865 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15865] in
                                                     (uu____15862, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15845 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15844 in
                                               uu____15841
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15881 =
                                                 let uu____15882 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15882.FStar_Syntax_Syntax.n in
                                               match uu____15881 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15888::uu____15889::[])
                                                   ->
                                                   let uu____15896 =
                                                     let uu____15899 =
                                                       let uu____15900 =
                                                         let uu____15907 =
                                                           let uu____15910 =
                                                             let uu____15911
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15911 in
                                                           let uu____15912 =
                                                             let uu____15915
                                                               =
                                                               let uu____15916
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15916 in
                                                             [uu____15915] in
                                                           uu____15910 ::
                                                             uu____15912 in
                                                         (bind1, uu____15907) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15900 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15899 in
                                                   uu____15896
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15924 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15930 =
                                                 let uu____15933 =
                                                   let uu____15934 =
                                                     let uu____15949 =
                                                       let uu____15952 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15953 =
                                                         let uu____15956 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15957 =
                                                           let uu____15960 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15961 =
                                                             let uu____15964
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15965
                                                               =
                                                               let uu____15968
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15969
                                                                 =
                                                                 let uu____15972
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15972] in
                                                               uu____15968 ::
                                                                 uu____15969 in
                                                             uu____15964 ::
                                                               uu____15965 in
                                                           uu____15960 ::
                                                             uu____15961 in
                                                         uu____15956 ::
                                                           uu____15957 in
                                                       uu____15952 ::
                                                         uu____15953 in
                                                     (bind_inst, uu____15949) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15934 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15933 in
                                               uu____15930
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15980 =
                                               FStar_List.tl stack in
                                             norm cfg env uu____15980 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____16004 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____16004 with
                            | (uu____16005,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____16040 =
                                        let uu____16041 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____16041.FStar_Syntax_Syntax.n in
                                      match uu____16040 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____16047) -> t4
                                      | uu____16052 -> head2 in
                                    let uu____16053 =
                                      let uu____16054 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____16054.FStar_Syntax_Syntax.n in
                                    match uu____16053 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____16060 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____16061 = maybe_extract_fv head2 in
                                  match uu____16061 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____16071 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____16071
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____16076 =
                                          maybe_extract_fv head3 in
                                        match uu____16076 with
                                        | FStar_Pervasives_Native.Some
                                            uu____16081 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____16082 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____16087 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____16102 =
                                    match uu____16102 with
                                    | (e,q) ->
                                        let uu____16109 =
                                          let uu____16110 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____16110.FStar_Syntax_Syntax.n in
                                        (match uu____16109 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____16125 -> false) in
                                  let uu____16126 =
                                    let uu____16127 =
                                      let uu____16134 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____16134 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____16127 in
                                  if uu____16126
                                  then
                                    let uu____16139 =
                                      let uu____16140 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____16140 in
                                    failwith uu____16139
                                  else ());
                                 (let uu____16142 =
                                    maybe_unfold_action head_app in
                                  match uu____16142 with
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
                                      let uu____16181 = FStar_List.tl stack in
                                      norm cfg env uu____16181 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16195 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16195 in
                           let uu____16196 = FStar_List.tl stack in
                           norm cfg env uu____16196 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16317  ->
                                     match uu____16317 with
                                     | (pat,wopt,tm) ->
                                         let uu____16365 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16365))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16397 = FStar_List.tl stack in
                           norm cfg env uu____16397 tm
                       | uu____16398 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16406 = should_reify cfg stack in
                    if uu____16406
                    then
                      let uu____16407 = FStar_List.tl stack in
                      let uu____16408 =
                        let uu____16409 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16409 in
                      norm cfg env uu____16407 uu____16408
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16412 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16412
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack in
                         let cfg1 =
                           let uu___136_16421 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___136_16421.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___136_16421.primitive_steps);
                             strong = (uu___136_16421.strong)
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
                | uu____16423 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____16425::uu____16426 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16431) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16432 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____16463 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16477 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16477
                             | uu____16488 -> m in
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
              let uu____16500 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16500 in
            let uu____16501 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16501 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16514  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16525  ->
                      let uu____16526 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16527 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16526
                        uu____16527);
                 (let t1 =
                    let uu____16529 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16529
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
                    | (UnivArgs (us',uu____16539))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____16594 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____16597 ->
                        let uu____16600 =
                          let uu____16601 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16601 in
                        failwith uu____16600
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
              let uu____16611 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16611 with
              | (uu____16612,return_repr) ->
                  let return_inst =
                    let uu____16621 =
                      let uu____16622 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16622.FStar_Syntax_Syntax.n in
                    match uu____16621 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16628::[]) ->
                        let uu____16635 =
                          let uu____16638 =
                            let uu____16639 =
                              let uu____16646 =
                                let uu____16649 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16649] in
                              (return_tm, uu____16646) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16639 in
                          FStar_Syntax_Syntax.mk uu____16638 in
                        uu____16635 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16657 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16660 =
                    let uu____16663 =
                      let uu____16664 =
                        let uu____16679 =
                          let uu____16682 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16683 =
                            let uu____16686 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16686] in
                          uu____16682 :: uu____16683 in
                        (return_inst, uu____16679) in
                      FStar_Syntax_Syntax.Tm_app uu____16664 in
                    FStar_Syntax_Syntax.mk uu____16663 in
                  uu____16660 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16695 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16695 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16698 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16698
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16699;
                     FStar_TypeChecker_Env.mtarget = uu____16700;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16701;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16716;
                     FStar_TypeChecker_Env.mtarget = uu____16717;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16718;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16742 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16743 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16742 t FStar_Syntax_Syntax.tun uu____16743)
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
                (fun uu____16799  ->
                   match uu____16799 with
                   | (a,imp) ->
                       let uu____16810 = norm cfg env [] a in
                       (uu____16810, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___137_16827 = comp1 in
            let uu____16830 =
              let uu____16831 =
                let uu____16840 = norm cfg env [] t in
                let uu____16841 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16840, uu____16841) in
              FStar_Syntax_Syntax.Total uu____16831 in
            {
              FStar_Syntax_Syntax.n = uu____16830;
              FStar_Syntax_Syntax.pos =
                (uu___137_16827.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16827.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___138_16856 = comp1 in
            let uu____16859 =
              let uu____16860 =
                let uu____16869 = norm cfg env [] t in
                let uu____16870 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16869, uu____16870) in
              FStar_Syntax_Syntax.GTotal uu____16860 in
            {
              FStar_Syntax_Syntax.n = uu____16859;
              FStar_Syntax_Syntax.pos =
                (uu___138_16856.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___138_16856.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16922  ->
                      match uu____16922 with
                      | (a,i) ->
                          let uu____16933 = norm cfg env [] a in
                          (uu____16933, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___84_16944  ->
                      match uu___84_16944 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16948 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16948
                      | f -> f)) in
            let uu___139_16952 = comp1 in
            let uu____16955 =
              let uu____16956 =
                let uu___140_16957 = ct in
                let uu____16958 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16959 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16962 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16958;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___140_16957.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16959;
                  FStar_Syntax_Syntax.effect_args = uu____16962;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16956 in
            {
              FStar_Syntax_Syntax.n = uu____16955;
              FStar_Syntax_Syntax.pos =
                (uu___139_16952.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_16952.FStar_Syntax_Syntax.vars)
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
            (let uu___141_16980 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___141_16980.tcenv);
               delta_level = (uu___141_16980.delta_level);
               primitive_steps = (uu___141_16980.primitive_steps);
               strong = (uu___141_16980.strong)
             }) env [] t in
        let non_info t =
          let uu____16985 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16985 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16988 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___142_17007 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___142_17007.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___142_17007.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____17014 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____17014
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
                    let uu___143_17025 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___143_17025.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___143_17025.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___143_17025.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags1
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___144_17027 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___144_17027.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___144_17027.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___144_17027.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___144_17027.FStar_Syntax_Syntax.flags)
                    } in
              let uu___145_17028 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___145_17028.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___145_17028.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____17030 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____17033  ->
        match uu____17033 with
        | (x,imp) ->
            let uu____17036 =
              let uu___146_17037 = x in
              let uu____17038 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___146_17037.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___146_17037.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17038
              } in
            (uu____17036, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17044 =
          FStar_List.fold_left
            (fun uu____17062  ->
               fun b  ->
                 match uu____17062 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____17044 with | (nbs,uu____17102) -> FStar_List.rev nbs
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
            let uu____17118 =
              let uu___147_17119 = rc in
              let uu____17120 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___147_17119.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17120;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___147_17119.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17118
        | uu____17127 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17140  ->
               let uu____17141 = FStar_Syntax_Print.tag_of_term t in
               let uu____17142 = FStar_Syntax_Print.term_to_string t in
               let uu____17143 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17150 =
                 let uu____17151 =
                   let uu____17154 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17154 in
                 stack_to_string uu____17151 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____17141 uu____17142 uu____17143 uu____17150);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____17183 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____17183
                 then
                   let time_now = FStar_Util.now () in
                   let uu____17185 =
                     let uu____17186 =
                       let uu____17187 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17187 in
                     FStar_Util.string_of_int uu____17186 in
                   let uu____17192 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17193 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17185 uu____17192 uu____17193
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___148_17211 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___148_17211.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___148_17211.strong)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____17260  ->
                     let uu____17261 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17261);
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
               let uu____17297 =
                 let uu___149_17298 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___149_17298.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___149_17298.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____17297
           | (Arg (Univ uu____17299,uu____17300,uu____17301))::uu____17302 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17305,uu____17306))::uu____17307 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____17323),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17376  ->
                     let uu____17377 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17377);
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
                  (let uu____17387 = FStar_ST.op_Bang m in
                   match uu____17387 with
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
                   | FStar_Pervasives_Native.Some (uu____17553,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17596 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17596
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17608  ->
                     let uu____17609 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17609);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17614 =
                   log cfg
                     (fun uu____17619  ->
                        let uu____17620 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17621 =
                          let uu____17622 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17639  ->
                                    match uu____17639 with
                                    | (p,uu____17649,uu____17650) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17622
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17620 uu____17621);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___85_17667  ->
                                match uu___85_17667 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17668 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___150_17672 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___150_17672.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___150_17672.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17704 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17725 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17785  ->
                                    fun uu____17786  ->
                                      match (uu____17785, uu____17786) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17877 = norm_pat env3 p1 in
                                          (match uu____17877 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17725 with
                           | (pats1,env3) ->
                               ((let uu___151_17959 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___151_17959.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___152_17978 = x in
                            let uu____17979 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_17978.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_17978.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17979
                            } in
                          ((let uu___153_17993 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___153_17993.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___154_18004 = x in
                            let uu____18005 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___154_18004.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___154_18004.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18005
                            } in
                          ((let uu___155_18019 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___155_18019.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___156_18035 = x in
                            let uu____18036 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___156_18035.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___156_18035.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18036
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___157_18043 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___157_18043.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18053 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18067 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____18067 with
                                  | (p,wopt,e) ->
                                      let uu____18087 = norm_pat env1 p in
                                      (match uu____18087 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18112 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18112 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____18118 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____18118) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18128) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18133 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18134;
                         FStar_Syntax_Syntax.fv_delta = uu____18135;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18136;
                         FStar_Syntax_Syntax.fv_delta = uu____18137;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18138);_}
                       -> true
                   | uu____18145 -> false in
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
                   let uu____18290 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18290 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18377 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18416 ->
                                 let uu____18417 =
                                   let uu____18418 = is_cons head1 in
                                   Prims.op_Negation uu____18418 in
                                 FStar_Util.Inr uu____18417)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18443 =
                              let uu____18444 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18444.FStar_Syntax_Syntax.n in
                            (match uu____18443 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18462 ->
                                 let uu____18463 =
                                   let uu____18464 = is_cons head1 in
                                   Prims.op_Negation uu____18464 in
                                 FStar_Util.Inr uu____18463))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18533)::rest_a,(p1,uu____18536)::rest_p) ->
                       let uu____18580 = matches_pat t1 p1 in
                       (match uu____18580 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18629 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18735 = matches_pat scrutinee1 p1 in
                       (match uu____18735 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18775  ->
                                  let uu____18776 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18777 =
                                    let uu____18778 =
                                      FStar_List.map
                                        (fun uu____18788  ->
                                           match uu____18788 with
                                           | (uu____18793,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18778
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18776 uu____18777);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18824  ->
                                       match uu____18824 with
                                       | (bv,t1) ->
                                           let uu____18847 =
                                             let uu____18854 =
                                               let uu____18857 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18857 in
                                             let uu____18858 =
                                               let uu____18859 =
                                                 let uu____18890 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18890, false) in
                                               Clos uu____18859 in
                                             (uu____18854, uu____18858) in
                                           uu____18847 :: env2) env1 s in
                              let uu____19007 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____19007))) in
                 let uu____19008 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____19008
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___86_19029  ->
                match uu___86_19029 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____19033 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____19039 -> d in
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
            let uu___158_19064 = config s e in
            {
              steps = (uu___158_19064.steps);
              tcenv = (uu___158_19064.tcenv);
              delta_level = (uu___158_19064.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___158_19064.strong)
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
      fun t  -> let uu____19089 = config s e in norm_comp uu____19089 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____19102 = config [] env in norm_universe uu____19102 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____19115 = config [] env in ghost_to_pure_aux uu____19115 [] c
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
        let uu____19133 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____19133 in
      let uu____19140 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____19140
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___159_19142 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___159_19142.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___159_19142.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____19145  ->
                    let uu____19146 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____19146))
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
            ((let uu____19163 =
                let uu____19168 =
                  let uu____19169 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19169 in
                (FStar_Errors.Warning_NormalizationFailure, uu____19168) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____19163);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19180 = config [AllowUnboundUniverses] env in
          norm_comp uu____19180 [] c
        with
        | e ->
            ((let uu____19193 =
                let uu____19198 =
                  let uu____19199 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19199 in
                (FStar_Errors.Warning_NormalizationFailure, uu____19198) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____19193);
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
                   let uu____19236 =
                     let uu____19237 =
                       let uu____19244 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____19244) in
                     FStar_Syntax_Syntax.Tm_refine uu____19237 in
                   mk uu____19236 t01.FStar_Syntax_Syntax.pos
               | uu____19249 -> t2)
          | uu____19250 -> t2 in
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
        let uu____19290 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19290 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19319 ->
                 let uu____19326 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19326 with
                  | (actuals,uu____19336,uu____19337) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19351 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19351 with
                         | (binders,args) ->
                             let uu____19368 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19368
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
      | uu____19376 ->
          let uu____19377 = FStar_Syntax_Util.head_and_args t in
          (match uu____19377 with
           | (head1,args) ->
               let uu____19414 =
                 let uu____19415 = FStar_Syntax_Subst.compress head1 in
                 uu____19415.FStar_Syntax_Syntax.n in
               (match uu____19414 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19418,thead) ->
                    let uu____19444 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19444 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19486 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___164_19494 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___164_19494.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___164_19494.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___164_19494.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___164_19494.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___164_19494.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___164_19494.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___164_19494.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___164_19494.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___164_19494.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___164_19494.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___164_19494.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___164_19494.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___164_19494.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___164_19494.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___164_19494.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___164_19494.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___164_19494.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___164_19494.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___164_19494.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___164_19494.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___164_19494.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___164_19494.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___164_19494.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___164_19494.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___164_19494.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___164_19494.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___164_19494.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___164_19494.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___164_19494.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___164_19494.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___164_19494.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19486 with
                            | (uu____19495,ty,uu____19497) ->
                                eta_expand_with_type env t ty))
                | uu____19498 ->
                    let uu____19499 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___165_19507 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___165_19507.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___165_19507.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___165_19507.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___165_19507.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___165_19507.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___165_19507.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___165_19507.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___165_19507.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___165_19507.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___165_19507.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___165_19507.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___165_19507.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___165_19507.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___165_19507.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___165_19507.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___165_19507.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___165_19507.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___165_19507.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___165_19507.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___165_19507.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___165_19507.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___165_19507.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___165_19507.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___165_19507.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___165_19507.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___165_19507.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___165_19507.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___165_19507.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___165_19507.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___165_19507.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___165_19507.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19499 with
                     | (uu____19508,ty,uu____19510) ->
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
            | (uu____19584,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19590,FStar_Util.Inl t) ->
                let uu____19596 =
                  let uu____19599 =
                    let uu____19600 =
                      let uu____19613 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19613) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19600 in
                  FStar_Syntax_Syntax.mk uu____19599 in
                uu____19596 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19617 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19617 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19644 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19699 ->
                    let uu____19700 =
                      let uu____19709 =
                        let uu____19710 = FStar_Syntax_Subst.compress t3 in
                        uu____19710.FStar_Syntax_Syntax.n in
                      (uu____19709, tc) in
                    (match uu____19700 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19735) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19772) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19811,FStar_Util.Inl uu____19812) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19835 -> failwith "Impossible") in
              (match uu____19644 with
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
          let uu____19940 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19940 with
          | (univ_names1,binders1,tc) ->
              let uu____19998 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19998)
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
          let uu____20033 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20033 with
          | (univ_names1,binders1,tc) ->
              let uu____20093 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20093)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20126 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20126 with
           | (univ_names1,binders1,typ1) ->
               let uu___166_20154 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___166_20154.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___166_20154.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___166_20154.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___166_20154.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___167_20175 = s in
          let uu____20176 =
            let uu____20177 =
              let uu____20186 = FStar_List.map (elim_uvars env) sigs in
              (uu____20186, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20177 in
          {
            FStar_Syntax_Syntax.sigel = uu____20176;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_20175.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_20175.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_20175.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_20175.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20203 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20203 with
           | (univ_names1,uu____20221,typ1) ->
               let uu___168_20235 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_20235.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_20235.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_20235.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_20235.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20241 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20241 with
           | (univ_names1,uu____20259,typ1) ->
               let uu___169_20273 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___169_20273.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___169_20273.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___169_20273.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___169_20273.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20307 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20307 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20330 =
                            let uu____20331 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20331 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20330 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___170_20334 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___170_20334.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___170_20334.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___171_20335 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___171_20335.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___171_20335.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___171_20335.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___171_20335.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___172_20347 = s in
          let uu____20348 =
            let uu____20349 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20349 in
          {
            FStar_Syntax_Syntax.sigel = uu____20348;
            FStar_Syntax_Syntax.sigrng =
              (uu___172_20347.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___172_20347.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___172_20347.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___172_20347.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20353 = elim_uvars_aux_t env us [] t in
          (match uu____20353 with
           | (us1,uu____20371,t1) ->
               let uu___173_20385 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___173_20385.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___173_20385.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___173_20385.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___173_20385.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20386 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20388 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20388 with
           | (univs1,binders,signature) ->
               let uu____20416 =
                 let uu____20425 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20425 with
                 | (univs_opening,univs2) ->
                     let uu____20452 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20452) in
               (match uu____20416 with
                | (univs_opening,univs_closing) ->
                    let uu____20469 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20475 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20476 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20475, uu____20476) in
                    (match uu____20469 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20498 =
                           match uu____20498 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20516 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20516 with
                                | (us1,t1) ->
                                    let uu____20527 =
                                      let uu____20532 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20539 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20532, uu____20539) in
                                    (match uu____20527 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20552 =
                                           let uu____20557 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20566 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20557, uu____20566) in
                                         (match uu____20552 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20582 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20582 in
                                              let uu____20583 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20583 with
                                               | (uu____20604,uu____20605,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20620 =
                                                       let uu____20621 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20621 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20620 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20626 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20626 with
                           | (uu____20639,uu____20640,t1) -> t1 in
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
                             | uu____20700 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20717 =
                               let uu____20718 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20718.FStar_Syntax_Syntax.n in
                             match uu____20717 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20777 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20806 =
                               let uu____20807 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20807.FStar_Syntax_Syntax.n in
                             match uu____20806 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20828) ->
                                 let uu____20849 = destruct_action_body body in
                                 (match uu____20849 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20894 ->
                                 let uu____20895 = destruct_action_body t in
                                 (match uu____20895 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20944 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20944 with
                           | (action_univs,t) ->
                               let uu____20953 = destruct_action_typ_templ t in
                               (match uu____20953 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___174_20994 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___174_20994.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___174_20994.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___175_20996 = ed in
                           let uu____20997 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20998 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20999 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21000 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21001 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21002 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21003 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21004 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21005 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21006 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21007 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21008 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21009 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21010 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___175_20996.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___175_20996.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20997;
                             FStar_Syntax_Syntax.bind_wp = uu____20998;
                             FStar_Syntax_Syntax.if_then_else = uu____20999;
                             FStar_Syntax_Syntax.ite_wp = uu____21000;
                             FStar_Syntax_Syntax.stronger = uu____21001;
                             FStar_Syntax_Syntax.close_wp = uu____21002;
                             FStar_Syntax_Syntax.assert_p = uu____21003;
                             FStar_Syntax_Syntax.assume_p = uu____21004;
                             FStar_Syntax_Syntax.null_wp = uu____21005;
                             FStar_Syntax_Syntax.trivial = uu____21006;
                             FStar_Syntax_Syntax.repr = uu____21007;
                             FStar_Syntax_Syntax.return_repr = uu____21008;
                             FStar_Syntax_Syntax.bind_repr = uu____21009;
                             FStar_Syntax_Syntax.actions = uu____21010
                           } in
                         let uu___176_21013 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___176_21013.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___176_21013.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___176_21013.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___176_21013.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___87_21030 =
            match uu___87_21030 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21057 = elim_uvars_aux_t env us [] t in
                (match uu____21057 with
                 | (us1,uu____21081,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___177_21100 = sub_eff in
            let uu____21101 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21104 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___177_21100.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___177_21100.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21101;
              FStar_Syntax_Syntax.lift = uu____21104
            } in
          let uu___178_21107 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___178_21107.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___178_21107.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___178_21107.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___178_21107.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____21117 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21117 with
           | (univ_names1,binders1,comp1) ->
               let uu___179_21151 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___179_21151.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___179_21151.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___179_21151.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___179_21151.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21162 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t