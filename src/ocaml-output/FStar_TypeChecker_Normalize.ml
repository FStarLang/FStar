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
    match projectee with | Arg _0 -> true | uu____831 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____869 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____907 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____966 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1010 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1068 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1110 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1144 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1192 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1240 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1269 .
    'Auu____1269 ->
      FStar_Range.range -> 'Auu____1269 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1320 = FStar_ST.op_Bang r in
      match uu____1320 with
      | FStar_Pervasives_Native.Some uu____1387 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1460 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1460 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___179_1468  ->
    match uu___179_1468 with
    | Arg (c,uu____1470,uu____1471) ->
        let uu____1472 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1472
    | MemoLazy uu____1473 -> "MemoLazy"
    | Abs (uu____1480,bs,uu____1482,uu____1483,uu____1484) ->
        let uu____1489 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1489
    | UnivArgs uu____1494 -> "UnivArgs"
    | Match uu____1501 -> "Match"
    | App (uu____1508,t,uu____1510,uu____1511) ->
        let uu____1512 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1512
    | Meta (m,uu____1514) -> "Meta"
    | Let uu____1515 -> "Let"
    | Steps (uu____1524,uu____1525,uu____1526) -> "Steps"
    | Debug (t,uu____1536) ->
        let uu____1537 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1537
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1546 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1546 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1564 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1564 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1579 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1579 then f () else ()
let is_empty: 'Auu____1585 . 'Auu____1585 Prims.list -> Prims.bool =
  fun uu___180_1591  ->
    match uu___180_1591 with | [] -> true | uu____1594 -> false
let lookup_bvar:
  'Auu____1605 'Auu____1606 .
    ('Auu____1606,'Auu____1605) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1605
  =
  fun env  ->
    fun x  ->
      try
        let uu____1630 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1630
      with
      | uu____1643 ->
          let uu____1644 =
            let uu____1645 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1645 in
          failwith uu____1644
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
          let uu____1686 =
            FStar_List.fold_left
              (fun uu____1712  ->
                 fun u1  ->
                   match uu____1712 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1737 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1737 with
                        | (k_u,n1) ->
                            let uu____1752 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1752
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1686 with
          | (uu____1770,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1795 =
                   let uu____1796 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1796 in
                 match uu____1795 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1814 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1823 ->
                   let uu____1824 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1824
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1830 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1839 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1848 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1855 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1855 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1872 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1872 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1880 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1888 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1888 with
                                  | (uu____1893,m) -> n1 <= m)) in
                        if uu____1880 then rest1 else us1
                    | uu____1898 -> us1)
               | uu____1903 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1907 = aux u3 in
              FStar_List.map (fun _0_41  -> FStar_Syntax_Syntax.U_succ _0_41)
                uu____1907 in
        let uu____1910 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1910
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1912 = aux u in
           match uu____1912 with
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
          (fun uu____2016  ->
             let uu____2017 = FStar_Syntax_Print.tag_of_term t in
             let uu____2018 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2017
               uu____2018);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2025 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2027 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2052 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2053 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2054 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2055 ->
                  let uu____2072 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2072
                  then
                    let uu____2073 =
                      let uu____2074 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2075 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2074 uu____2075 in
                    failwith uu____2073
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2078 =
                    let uu____2079 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2079 in
                  mk uu____2078 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2086 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2086
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2088 = lookup_bvar env x in
                  (match uu____2088 with
                   | Univ uu____2091 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2095) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2207 = closures_as_binders_delayed cfg env bs in
                  (match uu____2207 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2235 =
                         let uu____2236 =
                           let uu____2253 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2253) in
                         FStar_Syntax_Syntax.Tm_abs uu____2236 in
                       mk uu____2235 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2284 = closures_as_binders_delayed cfg env bs in
                  (match uu____2284 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2326 =
                    let uu____2337 =
                      let uu____2344 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2344] in
                    closures_as_binders_delayed cfg env uu____2337 in
                  (match uu____2326 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2362 =
                         let uu____2363 =
                           let uu____2370 =
                             let uu____2371 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2371
                               FStar_Pervasives_Native.fst in
                           (uu____2370, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2363 in
                       mk uu____2362 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2462 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2462
                    | FStar_Util.Inr c ->
                        let uu____2476 = close_comp cfg env c in
                        FStar_Util.Inr uu____2476 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2492 =
                    let uu____2493 =
                      let uu____2520 = closure_as_term_delayed cfg env t11 in
                      (uu____2520, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2493 in
                  mk uu____2492 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2571 =
                    let uu____2572 =
                      let uu____2579 = closure_as_term_delayed cfg env t' in
                      let uu____2582 =
                        let uu____2583 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2583 in
                      (uu____2579, uu____2582) in
                    FStar_Syntax_Syntax.Tm_meta uu____2572 in
                  mk uu____2571 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2643 =
                    let uu____2644 =
                      let uu____2651 = closure_as_term_delayed cfg env t' in
                      let uu____2654 =
                        let uu____2655 =
                          let uu____2662 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2662) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2655 in
                      (uu____2651, uu____2654) in
                    FStar_Syntax_Syntax.Tm_meta uu____2644 in
                  mk uu____2643 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2681 =
                    let uu____2682 =
                      let uu____2689 = closure_as_term_delayed cfg env t' in
                      let uu____2692 =
                        let uu____2693 =
                          let uu____2702 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2702) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2693 in
                      (uu____2689, uu____2692) in
                    FStar_Syntax_Syntax.Tm_meta uu____2682 in
                  mk uu____2681 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2715 =
                    let uu____2716 =
                      let uu____2723 = closure_as_term_delayed cfg env t' in
                      (uu____2723, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2716 in
                  mk uu____2715 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2763  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2782 =
                    let uu____2793 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2793
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2812 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___199_2824 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___199_2824.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___199_2824.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2812)) in
                  (match uu____2782 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___200_2840 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___200_2840.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___200_2840.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2851,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2910  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2935 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2935
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2955  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2977 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2977
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___201_2989 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___201_2989.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___201_2989.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_42  -> FStar_Util.Inl _0_42)) in
                    let uu___202_2990 = lb in
                    let uu____2991 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___202_2990.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___202_2990.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2991
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3021  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3110 =
                    match uu____3110 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3165 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3186 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3246  ->
                                        fun uu____3247  ->
                                          match (uu____3246, uu____3247) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3338 =
                                                norm_pat env3 p1 in
                                              (match uu____3338 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3186 with
                               | (pats1,env3) ->
                                   ((let uu___203_3420 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___203_3420.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___204_3439 = x in
                                let uu____3440 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___204_3439.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___204_3439.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3440
                                } in
                              ((let uu___205_3454 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___205_3454.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___206_3465 = x in
                                let uu____3466 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___206_3465.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___206_3465.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3466
                                } in
                              ((let uu___207_3480 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___207_3480.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___208_3496 = x in
                                let uu____3497 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___208_3496.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___208_3496.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3497
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___209_3504 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___209_3504.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3507 = norm_pat env1 pat in
                        (match uu____3507 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3536 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3536 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3542 =
                    let uu____3543 =
                      let uu____3566 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3566) in
                    FStar_Syntax_Syntax.Tm_match uu____3543 in
                  mk uu____3542 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3652 -> closure_as_term cfg env t
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
        | uu____3678 ->
            FStar_List.map
              (fun uu____3695  ->
                 match uu____3695 with
                 | (x,imp) ->
                     let uu____3714 = closure_as_term_delayed cfg env x in
                     (uu____3714, imp)) args
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
        let uu____3728 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3777  ->
                  fun uu____3778  ->
                    match (uu____3777, uu____3778) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___210_3848 = b in
                          let uu____3849 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___210_3848.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___210_3848.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3849
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3728 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3942 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3955 = closure_as_term_delayed cfg env t in
                 let uu____3956 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3955 uu____3956
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3969 = closure_as_term_delayed cfg env t in
                 let uu____3970 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3969 uu____3970
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
                        (fun uu___181_3996  ->
                           match uu___181_3996 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4000 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4000
                           | f -> f)) in
                 let uu____4004 =
                   let uu___211_4005 = c1 in
                   let uu____4006 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4006;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___211_4005.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4004)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___182_4016  ->
            match uu___182_4016 with
            | FStar_Syntax_Syntax.DECREASES uu____4017 -> false
            | uu____4020 -> true))
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
                   (fun uu___183_4038  ->
                      match uu___183_4038 with
                      | FStar_Syntax_Syntax.DECREASES uu____4039 -> false
                      | uu____4042 -> true)) in
            let rc1 =
              let uu___212_4044 = rc in
              let uu____4045 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___212_4044.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4045;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4052 -> lopt
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
    let uu____4140 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4140 in
  let arg_as_bounded_int uu____4168 =
    match uu____4168 with
    | (a,uu____4180) ->
        let uu____4187 =
          let uu____4188 = FStar_Syntax_Subst.compress a in
          uu____4188.FStar_Syntax_Syntax.n in
        (match uu____4187 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4198;
                FStar_Syntax_Syntax.vars = uu____4199;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4201;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4202;_},uu____4203)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4242 =
               let uu____4247 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4247) in
             FStar_Pervasives_Native.Some uu____4242
         | uu____4252 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4294 = f a in FStar_Pervasives_Native.Some uu____4294
    | uu____4295 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4345 = f a0 a1 in FStar_Pervasives_Native.Some uu____4345
    | uu____4346 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4395 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4395 in
  let binary_op as_a f res args =
    let uu____4451 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4451 in
  let as_primitive_step uu____4475 =
    match uu____4475 with
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
           let uu____4523 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4523) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4551 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4551) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4572 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4572) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4600 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4600) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4628 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4628) in
  let list_of_string' rng s =
    let name l =
      let uu____4642 =
        let uu____4643 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4643 in
      mk uu____4642 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4653 =
      let uu____4656 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4656 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4653 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4686 =
      let uu____4687 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4687 in
    FStar_Syntax_Embeddings.embed_int rng uu____4686 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4705 = arg_as_string a1 in
        (match uu____4705 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4711 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4711 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4724 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4724
              | uu____4725 -> FStar_Pervasives_Native.None)
         | uu____4730 -> FStar_Pervasives_Native.None)
    | uu____4733 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4743 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4743 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4767 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4778 =
          let uu____4799 = arg_as_string fn in
          let uu____4802 = arg_as_int from_line in
          let uu____4805 = arg_as_int from_col in
          let uu____4808 = arg_as_int to_line in
          let uu____4811 = arg_as_int to_col in
          (uu____4799, uu____4802, uu____4805, uu____4808, uu____4811) in
        (match uu____4778 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4842 =
                 let uu____4843 = FStar_BigInt.to_int_fs from_l in
                 let uu____4844 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4843 uu____4844 in
               let uu____4845 =
                 let uu____4846 = FStar_BigInt.to_int_fs to_l in
                 let uu____4847 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4846 uu____4847 in
               FStar_Range.mk_range fn1 uu____4842 uu____4845 in
             let uu____4848 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4848
         | uu____4853 -> FStar_Pervasives_Native.None)
    | uu____4874 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4901)::(a1,uu____4903)::(a2,uu____4905)::[] ->
        let uu____4942 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4942 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4955 -> FStar_Pervasives_Native.None)
    | uu____4956 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4983)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4992 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5016 =
      let uu____5031 =
        let uu____5046 =
          let uu____5061 =
            let uu____5076 =
              let uu____5091 =
                let uu____5106 =
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
                                            let uu____5314 =
                                              FStar_Parser_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____5314,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____5321 =
                                            let uu____5336 =
                                              let uu____5349 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____5349,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list
                                                      FStar_Syntax_Embeddings.unembed_char_safe)
                                                   string_of_list')) in
                                            let uu____5358 =
                                              let uu____5373 =
                                                let uu____5388 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____5388,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              let uu____5397 =
                                                let uu____5414 =
                                                  let uu____5429 =
                                                    FStar_Parser_Const.p2l
                                                      ["Prims"; "mk_range"] in
                                                  (uu____5429,
                                                    (Prims.parse_int "5"),
                                                    mk_range1) in
                                                let uu____5438 =
                                                  let uu____5455 =
                                                    let uu____5474 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "Range";
                                                        "prims_to_fstar_range"] in
                                                    (uu____5474,
                                                      (Prims.parse_int "1"),
                                                      idstep) in
                                                  [uu____5455] in
                                                uu____5414 :: uu____5438 in
                                              uu____5373 :: uu____5397 in
                                            uu____5336 :: uu____5358 in
                                          uu____5301 :: uu____5321 in
                                        (FStar_Parser_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____5286 in
                                      (FStar_Parser_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____5271 in
                                    (FStar_Parser_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____5256 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____5241 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____5226 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5211 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5196 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5181 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5166 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5151 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5810 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5810)))
                      :: uu____5136 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5836 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5836)))
                    :: uu____5121 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5862 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5862)))
                  :: uu____5106 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5888 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5888)))
                :: uu____5091 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5076 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5061 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5046 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5031 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5016 in
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
      let uu____6038 =
        let uu____6039 =
          let uu____6040 = FStar_Syntax_Syntax.as_arg c in [uu____6040] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6039 in
      uu____6038 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6075 =
              let uu____6088 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6088, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6108  ->
                        fun uu____6109  ->
                          match (uu____6108, uu____6109) with
                          | ((int_to_t1,x),(uu____6128,y)) ->
                              let uu____6138 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6138))) in
            let uu____6139 =
              let uu____6154 =
                let uu____6167 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6167, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6187  ->
                          fun uu____6188  ->
                            match (uu____6187, uu____6188) with
                            | ((int_to_t1,x),(uu____6207,y)) ->
                                let uu____6217 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6217))) in
              let uu____6218 =
                let uu____6233 =
                  let uu____6246 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6246, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6266  ->
                            fun uu____6267  ->
                              match (uu____6266, uu____6267) with
                              | ((int_to_t1,x),(uu____6286,y)) ->
                                  let uu____6296 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6296))) in
                [uu____6233] in
              uu____6154 :: uu____6218 in
            uu____6075 :: uu____6139)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6386)::(a1,uu____6388)::(a2,uu____6390)::[] ->
        let uu____6427 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6427 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___213_6433 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___213_6433.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___213_6433.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___214_6437 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_6437.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_6437.FStar_Syntax_Syntax.vars)
                })
         | uu____6438 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6440)::uu____6441::(a1,uu____6443)::(a2,uu____6445)::[] ->
        let uu____6494 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6494 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___213_6500 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___213_6500.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___213_6500.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___214_6504 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_6504.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_6504.FStar_Syntax_Syntax.vars)
                })
         | uu____6505 -> FStar_Pervasives_Native.None)
    | uu____6506 -> failwith "Unexpected number of arguments" in
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
      let uu____6526 =
        let uu____6527 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6527 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6526
    with | uu____6533 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6540 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6540) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6600  ->
           fun subst1  ->
             match uu____6600 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6642)) ->
                      let uu____6701 = b in
                      (match uu____6701 with
                       | (bv,uu____6709) ->
                           let uu____6710 =
                             let uu____6711 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6711 in
                           if uu____6710
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6716 = unembed_binder term1 in
                              match uu____6716 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6723 =
                                      let uu___217_6724 = bv in
                                      let uu____6725 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___217_6724.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___217_6724.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6725
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6723 in
                                  let b_for_x =
                                    let uu____6729 =
                                      let uu____6736 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6736) in
                                    FStar_Syntax_Syntax.NT uu____6729 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___184_6745  ->
                                         match uu___184_6745 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6746,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6748;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6749;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6754 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6755 -> subst1)) env []
let reduce_primops:
  'Auu____6778 'Auu____6779 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6779) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6778 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____6820 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6820
          then tm
          else
            (let uu____6822 = FStar_Syntax_Util.head_and_args tm in
             match uu____6822 with
             | (head1,args) ->
                 let uu____6859 =
                   let uu____6860 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6860.FStar_Syntax_Syntax.n in
                 (match uu____6859 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6864 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6864 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6881  ->
                                   let uu____6882 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6883 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6890 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6882 uu____6883 uu____6890);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6895  ->
                                   let uu____6896 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6896);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6899  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6901 =
                                 prim_step.interpretation psc args in
                               match uu____6901 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6907  ->
                                         let uu____6908 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6908);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6914  ->
                                         let uu____6915 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6916 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6915 uu____6916);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6917 ->
                           (log_primops cfg
                              (fun uu____6921  ->
                                 let uu____6922 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6922);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6926  ->
                            let uu____6927 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6927);
                       (match args with
                        | (a1,uu____6929)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6946 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6958  ->
                            let uu____6959 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6959);
                       (match args with
                        | (a1,uu____6961)::(a2,uu____6963)::[] ->
                            let uu____6990 =
                              FStar_Syntax_Embeddings.unembed_range a2 in
                            (match uu____6990 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___218_6994 = a1 in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___218_6994.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___218_6994.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6997 -> tm))
                  | uu____7006 -> tm))
let reduce_equality:
  'Auu____7017 'Auu____7018 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7018) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7017 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___219_7056 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___219_7056.tcenv);
           delta_level = (uu___219_7056.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___219_7056.strong)
         }) tm
let maybe_simplify:
  'Auu____7069 'Auu____7070 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7070) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7069 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7112 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7112
          then tm1
          else
            (let w t =
               let uu___220_7124 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___220_7124.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___220_7124.FStar_Syntax_Syntax.vars)
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
               | uu____7141 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7181;
                         FStar_Syntax_Syntax.vars = uu____7182;_},uu____7183);
                    FStar_Syntax_Syntax.pos = uu____7184;
                    FStar_Syntax_Syntax.vars = uu____7185;_},args)
                 ->
                 let uu____7211 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7211
                 then
                   let uu____7212 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7212 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7267)::
                        (uu____7268,(arg,uu____7270))::[] -> arg
                    | (uu____7335,(arg,uu____7337))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7338)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7403)::uu____7404::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7467::(FStar_Pervasives_Native.Some (false
                                   ),uu____7468)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7531 -> tm1)
                 else
                   (let uu____7547 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7547
                    then
                      let uu____7548 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7548 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7603)::uu____7604::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7667::(FStar_Pervasives_Native.Some (true
                                     ),uu____7668)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7731)::
                          (uu____7732,(arg,uu____7734))::[] -> arg
                      | (uu____7799,(arg,uu____7801))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7802)::[]
                          -> arg
                      | uu____7867 -> tm1
                    else
                      (let uu____7883 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7883
                       then
                         let uu____7884 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7884 with
                         | uu____7939::(FStar_Pervasives_Native.Some (true
                                        ),uu____7940)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8003)::uu____8004::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8067)::
                             (uu____8068,(arg,uu____8070))::[] -> arg
                         | (uu____8135,(p,uu____8137))::(uu____8138,(q,uu____8140))::[]
                             ->
                             let uu____8205 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8205
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8207 -> tm1
                       else
                         (let uu____8223 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8223
                          then
                            let uu____8224 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8224 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8279)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8318)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8357 -> tm1
                          else
                            (let uu____8373 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8373
                             then
                               match args with
                               | (t,uu____8375)::[] ->
                                   let uu____8392 =
                                     let uu____8393 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8393.FStar_Syntax_Syntax.n in
                                   (match uu____8392 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8396::[],body,uu____8398) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8425 -> tm1)
                                    | uu____8428 -> tm1)
                               | (uu____8429,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8430))::
                                   (t,uu____8432)::[] ->
                                   let uu____8471 =
                                     let uu____8472 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8472.FStar_Syntax_Syntax.n in
                                   (match uu____8471 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8475::[],body,uu____8477) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8504 -> tm1)
                                    | uu____8507 -> tm1)
                               | uu____8508 -> tm1
                             else
                               (let uu____8518 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8518
                                then
                                  match args with
                                  | (t,uu____8520)::[] ->
                                      let uu____8537 =
                                        let uu____8538 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8538.FStar_Syntax_Syntax.n in
                                      (match uu____8537 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8541::[],body,uu____8543)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8570 -> tm1)
                                       | uu____8573 -> tm1)
                                  | (uu____8574,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8575))::(t,uu____8577)::[] ->
                                      let uu____8616 =
                                        let uu____8617 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8617.FStar_Syntax_Syntax.n in
                                      (match uu____8616 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8620::[],body,uu____8622)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8649 -> tm1)
                                       | uu____8652 -> tm1)
                                  | uu____8653 -> tm1
                                else
                                  (let uu____8663 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8663
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8664;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8665;_},uu____8666)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8683;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8684;_},uu____8685)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8702 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8713;
                    FStar_Syntax_Syntax.vars = uu____8714;_},args)
                 ->
                 let uu____8736 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8736
                 then
                   let uu____8737 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8737 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8792)::
                        (uu____8793,(arg,uu____8795))::[] -> arg
                    | (uu____8860,(arg,uu____8862))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8863)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8928)::uu____8929::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8992::(FStar_Pervasives_Native.Some (false
                                   ),uu____8993)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9056 -> tm1)
                 else
                   (let uu____9072 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9072
                    then
                      let uu____9073 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9073 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9128)::uu____9129::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9192::(FStar_Pervasives_Native.Some (true
                                     ),uu____9193)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9256)::
                          (uu____9257,(arg,uu____9259))::[] -> arg
                      | (uu____9324,(arg,uu____9326))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9327)::[]
                          -> arg
                      | uu____9392 -> tm1
                    else
                      (let uu____9408 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9408
                       then
                         let uu____9409 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9409 with
                         | uu____9464::(FStar_Pervasives_Native.Some (true
                                        ),uu____9465)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9528)::uu____9529::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9592)::
                             (uu____9593,(arg,uu____9595))::[] -> arg
                         | (uu____9660,(p,uu____9662))::(uu____9663,(q,uu____9665))::[]
                             ->
                             let uu____9730 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9730
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9732 -> tm1
                       else
                         (let uu____9748 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9748
                          then
                            let uu____9749 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9749 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9804)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9843)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9882 -> tm1
                          else
                            (let uu____9898 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9898
                             then
                               match args with
                               | (t,uu____9900)::[] ->
                                   let uu____9917 =
                                     let uu____9918 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9918.FStar_Syntax_Syntax.n in
                                   (match uu____9917 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9921::[],body,uu____9923) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9950 -> tm1)
                                    | uu____9953 -> tm1)
                               | (uu____9954,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9955))::
                                   (t,uu____9957)::[] ->
                                   let uu____9996 =
                                     let uu____9997 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9997.FStar_Syntax_Syntax.n in
                                   (match uu____9996 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10000::[],body,uu____10002) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10029 -> tm1)
                                    | uu____10032 -> tm1)
                               | uu____10033 -> tm1
                             else
                               (let uu____10043 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10043
                                then
                                  match args with
                                  | (t,uu____10045)::[] ->
                                      let uu____10062 =
                                        let uu____10063 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10063.FStar_Syntax_Syntax.n in
                                      (match uu____10062 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10066::[],body,uu____10068)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10095 -> tm1)
                                       | uu____10098 -> tm1)
                                  | (uu____10099,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10100))::(t,uu____10102)::[] ->
                                      let uu____10141 =
                                        let uu____10142 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10142.FStar_Syntax_Syntax.n in
                                      (match uu____10141 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10145::[],body,uu____10147)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10174 -> tm1)
                                       | uu____10177 -> tm1)
                                  | uu____10178 -> tm1
                                else
                                  (let uu____10188 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10188
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10189;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10190;_},uu____10191)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10208;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10209;_},uu____10210)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10227 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | uu____10237 -> tm1)
let is_norm_request:
  'Auu____10244 .
    FStar_Syntax_Syntax.term -> 'Auu____10244 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10257 =
        let uu____10264 =
          let uu____10265 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10265.FStar_Syntax_Syntax.n in
        (uu____10264, args) in
      match uu____10257 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10271::uu____10272::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10276::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10281::uu____10282::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10285 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___185_10297  ->
    match uu___185_10297 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10303 =
          let uu____10306 =
            let uu____10307 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10307 in
          [uu____10306] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10303
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10326 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10326) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10364 =
          let uu____10367 =
            let uu____10372 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10372 s in
          FStar_All.pipe_right uu____10367 FStar_Util.must in
        FStar_All.pipe_right uu____10364 tr_norm_steps in
      match args with
      | uu____10397::(tm,uu____10399)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10422)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10437)::uu____10438::(tm,uu____10440)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10480 =
              let uu____10483 = full_norm steps in parse_steps uu____10483 in
            Beta :: uu____10480 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10492 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___186_10510  ->
    match uu___186_10510 with
    | (App
        (uu____10513,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10514;
                       FStar_Syntax_Syntax.vars = uu____10515;_},uu____10516,uu____10517))::uu____10518
        -> true
    | uu____10525 -> false
let firstn:
  'Auu____10534 .
    Prims.int ->
      'Auu____10534 Prims.list ->
        ('Auu____10534 Prims.list,'Auu____10534 Prims.list)
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
          (uu____10572,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10573;
                         FStar_Syntax_Syntax.vars = uu____10574;_},uu____10575,uu____10576))::uu____10577
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10584 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10700  ->
               let uu____10701 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10702 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10703 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10710 =
                 let uu____10711 =
                   let uu____10714 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10714 in
                 stack_to_string uu____10711 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10701 uu____10702 uu____10703 uu____10710);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10737 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10762 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10779 =
                 let uu____10780 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10781 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10780 uu____10781 in
               failwith uu____10779
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10782 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10799 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10800 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10801;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10802;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10805;
                 FStar_Syntax_Syntax.fv_delta = uu____10806;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10807;
                 FStar_Syntax_Syntax.fv_delta = uu____10808;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10809);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10817 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10817 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____10823  ->
                     let uu____10824 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10825 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10824 uu____10825);
                if b
                then
                  (let uu____10826 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____10826 t1 fv)
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
                 let uu___221_10865 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___221_10865.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___221_10865.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10898 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10898) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___222_10906 = cfg in
                 let uu____10907 =
                   FStar_List.filter
                     (fun uu___187_10910  ->
                        match uu___187_10910 with
                        | UnfoldOnly uu____10911 -> false
                        | NoDeltaSteps  -> false
                        | uu____10914 -> true) cfg.steps in
                 {
                   steps = uu____10907;
                   tcenv = (uu___222_10906.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___222_10906.primitive_steps);
                   strong = (uu___222_10906.strong)
                 } in
               let uu____10915 = get_norm_request (norm cfg' env []) args in
               (match uu____10915 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10931 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___188_10936  ->
                                match uu___188_10936 with
                                | UnfoldUntil uu____10937 -> true
                                | UnfoldOnly uu____10938 -> true
                                | uu____10941 -> false)) in
                      if uu____10931
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___223_10946 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___223_10946.tcenv);
                        delta_level;
                        primitive_steps = (uu___223_10946.primitive_steps);
                        strong = (uu___223_10946.strong)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10957 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10957
                      then
                        let uu____10960 =
                          let uu____10961 =
                            let uu____10966 = FStar_Util.now () in
                            (t1, uu____10966) in
                          Debug uu____10961 in
                        uu____10960 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____10968;
                  FStar_Syntax_Syntax.vars = uu____10969;_},a1::a2::rest)
               ->
               let uu____11017 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11017 with
                | (hd1,uu____11033) ->
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
                  FStar_Syntax_Syntax.pos = uu____11098;
                  FStar_Syntax_Syntax.vars = uu____11099;_},a1::a2::rest)
               ->
               let uu____11147 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11147 with
                | (hd1,uu____11163) ->
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
                  FStar_Syntax_Syntax.pos = uu____11228;
                  FStar_Syntax_Syntax.vars = uu____11229;_},a1::a2::a3::rest)
               ->
               let uu____11290 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11290 with
                | (hd1,uu____11306) ->
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
                    (FStar_Const.Const_reflect uu____11377);
                  FStar_Syntax_Syntax.pos = uu____11378;
                  FStar_Syntax_Syntax.vars = uu____11379;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11411 = FStar_List.tl stack1 in
               norm cfg env uu____11411 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11414;
                  FStar_Syntax_Syntax.vars = uu____11415;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11447 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11447 with
                | (reify_head,uu____11463) ->
                    let a1 =
                      let uu____11485 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11485 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11488);
                            FStar_Syntax_Syntax.pos = uu____11489;
                            FStar_Syntax_Syntax.vars = uu____11490;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11524 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11534 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11534
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11541 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11541
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11544 =
                      let uu____11551 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11551, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11544 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___189_11564  ->
                         match uu___189_11564 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11567 =
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
                 if uu____11567
                 then false
                 else
                   (let uu____11569 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___190_11576  ->
                              match uu___190_11576 with
                              | UnfoldOnly uu____11577 -> true
                              | uu____11580 -> false)) in
                    match uu____11569 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11584 -> should_delta) in
               (log cfg
                  (fun uu____11592  ->
                     let uu____11593 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11594 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11595 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11593 uu____11594 uu____11595);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11598 = lookup_bvar env x in
               (match uu____11598 with
                | Univ uu____11601 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11650 = FStar_ST.op_Bang r in
                      (match uu____11650 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11787  ->
                                 let uu____11788 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11789 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11788
                                   uu____11789);
                            (let uu____11790 =
                               let uu____11791 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11791.FStar_Syntax_Syntax.n in
                             match uu____11790 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11794 ->
                                 norm cfg env2 stack1 t'
                             | uu____11811 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11869)::uu____11870 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11879)::uu____11880 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11890,uu____11891))::stack_rest ->
                    (match c with
                     | Univ uu____11895 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11904 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11925  ->
                                    let uu____11926 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11926);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11966  ->
                                    let uu____11967 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11967);
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
                      (let uu___224_12017 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___224_12017.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___224_12017.strong)
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12050  ->
                          let uu____12051 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12051);
                     norm cfg env stack2 t1)
                | (Debug uu____12052)::uu____12053 ->
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
                                   (let uu___225_12147 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12147.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12147.FStar_Syntax_Syntax.residual_flags)
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
                               let uu___226_12168 = cfg in
                               {
                                 steps = (uu___226_12168.steps);
                                 tcenv = (uu___226_12168.tcenv);
                                 delta_level = (uu___226_12168.delta_level);
                                 primitive_steps =
                                   (uu___226_12168.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____12179)::uu____12180 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12187 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12187
                    else
                      (let uu____12189 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12189 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12231  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12259 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12259
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12269 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12269)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12274 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12274.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12274.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12275 -> lopt in
                           (log cfg
                              (fun uu____12281  ->
                                 let uu____12282 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12282);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12295 = cfg in
                               {
                                 steps = (uu___226_12295.steps);
                                 tcenv = (uu___226_12295.tcenv);
                                 delta_level = (uu___226_12295.delta_level);
                                 primitive_steps =
                                   (uu___226_12295.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____12306)::uu____12307 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12318 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12318
                    else
                      (let uu____12320 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12320 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12362  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12390 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12390
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12400 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12400)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12405 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12405.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12405.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12406 -> lopt in
                           (log cfg
                              (fun uu____12412  ->
                                 let uu____12413 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12413);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12426 = cfg in
                               {
                                 steps = (uu___226_12426.steps);
                                 tcenv = (uu___226_12426.tcenv);
                                 delta_level = (uu___226_12426.delta_level);
                                 primitive_steps =
                                   (uu___226_12426.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12437)::uu____12438 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12449 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12449
                    else
                      (let uu____12451 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12451 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12493  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12521 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12521
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12531 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12531)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12536 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12536.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12536.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12537 -> lopt in
                           (log cfg
                              (fun uu____12543  ->
                                 let uu____12544 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12544);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12557 = cfg in
                               {
                                 steps = (uu___226_12557.steps);
                                 tcenv = (uu___226_12557.tcenv);
                                 delta_level = (uu___226_12557.delta_level);
                                 primitive_steps =
                                   (uu___226_12557.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12568)::uu____12569 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12584 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12584
                    else
                      (let uu____12586 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12586 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12628  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12656 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12656
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12666 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12666)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12671 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12671.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12671.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12672 -> lopt in
                           (log cfg
                              (fun uu____12678  ->
                                 let uu____12679 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12679);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12692 = cfg in
                               {
                                 steps = (uu___226_12692.steps);
                                 tcenv = (uu___226_12692.tcenv);
                                 delta_level = (uu___226_12692.delta_level);
                                 primitive_steps =
                                   (uu___226_12692.primitive_steps);
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
                      let uu____12703 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12703
                    else
                      (let uu____12705 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12705 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12747  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12775 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12775
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12785 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12785)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___225_12790 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___225_12790.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___225_12790.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12791 -> lopt in
                           (log cfg
                              (fun uu____12797  ->
                                 let uu____12798 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12798);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___226_12811 = cfg in
                               {
                                 steps = (uu___226_12811.steps);
                                 tcenv = (uu___226_12811.tcenv);
                                 delta_level = (uu___226_12811.delta_level);
                                 primitive_steps =
                                   (uu___226_12811.primitive_steps);
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
                      (fun uu____12860  ->
                         fun stack2  ->
                           match uu____12860 with
                           | (a,aq) ->
                               let uu____12872 =
                                 let uu____12873 =
                                   let uu____12880 =
                                     let uu____12881 =
                                       let uu____12912 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12912, false) in
                                     Clos uu____12881 in
                                   (uu____12880, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12873 in
                               uu____12872 :: stack2) args) in
               (log cfg
                  (fun uu____12988  ->
                     let uu____12989 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12989);
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
                             ((let uu___227_13025 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___227_13025.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___227_13025.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____13026 ->
                      let uu____13031 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13031)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13034 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13034 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13065 =
                          let uu____13066 =
                            let uu____13073 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___228_13075 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___228_13075.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___228_13075.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13073) in
                          FStar_Syntax_Syntax.Tm_refine uu____13066 in
                        mk uu____13065 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13094 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____13094
               else
                 (let uu____13096 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13096 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13104 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13128  -> dummy :: env1) env) in
                        norm_comp cfg uu____13104 c1 in
                      let t2 =
                        let uu____13150 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13150 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13209)::uu____13210 ->
                    (log cfg
                       (fun uu____13221  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13222)::uu____13223 ->
                    (log cfg
                       (fun uu____13234  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13235,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13236;
                                   FStar_Syntax_Syntax.vars = uu____13237;_},uu____13238,uu____13239))::uu____13240
                    ->
                    (log cfg
                       (fun uu____13249  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13250)::uu____13251 ->
                    (log cfg
                       (fun uu____13262  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13263 ->
                    (log cfg
                       (fun uu____13266  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13270  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13287 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13287
                         | FStar_Util.Inr c ->
                             let uu____13295 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13295 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13301 =
                         let uu____13302 =
                           let uu____13303 =
                             let uu____13330 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13330, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13303 in
                         mk uu____13302 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13301))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13406,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13407;
                               FStar_Syntax_Syntax.lbunivs = uu____13408;
                               FStar_Syntax_Syntax.lbtyp = uu____13409;
                               FStar_Syntax_Syntax.lbeff = uu____13410;
                               FStar_Syntax_Syntax.lbdef = uu____13411;_}::uu____13412),uu____13413)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13449 =
                 (let uu____13452 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13452) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13454 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13454))) in
               if uu____13449
               then
                 let binder =
                   let uu____13456 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13456 in
                 let env1 =
                   let uu____13466 =
                     let uu____13473 =
                       let uu____13474 =
                         let uu____13505 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13505,
                           false) in
                       Clos uu____13474 in
                     ((FStar_Pervasives_Native.Some binder), uu____13473) in
                   uu____13466 :: env in
                 (log cfg
                    (fun uu____13590  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13592 =
                    let uu____13597 =
                      let uu____13598 =
                        let uu____13599 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13599
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13598] in
                    FStar_Syntax_Subst.open_term uu____13597 body in
                  match uu____13592 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13608  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13616 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13616 in
                          FStar_Util.Inl
                            (let uu___229_13626 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___229_13626.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___229_13626.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13629  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___230_13631 = lb in
                           let uu____13632 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___230_13631.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___230_13631.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13632
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13667  -> dummy :: env1) env) in
                         let cfg1 =
                           let uu___231_13687 = cfg in
                           {
                             steps = (uu___231_13687.steps);
                             tcenv = (uu___231_13687.tcenv);
                             delta_level = (uu___231_13687.delta_level);
                             primitive_steps =
                               (uu___231_13687.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13690  ->
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
               let uu____13707 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13707 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13743 =
                               let uu___232_13744 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___232_13744.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___232_13744.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13743 in
                           let uu____13745 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13745 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13771 =
                                   FStar_List.map (fun uu____13787  -> dummy)
                                     lbs1 in
                                 let uu____13788 =
                                   let uu____13797 =
                                     FStar_List.map
                                       (fun uu____13817  -> dummy) xs1 in
                                   FStar_List.append uu____13797 env in
                                 FStar_List.append uu____13771 uu____13788 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13841 =
                                       let uu___233_13842 = rc in
                                       let uu____13843 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___233_13842.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13843;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___233_13842.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13841
                                 | uu____13850 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___234_13854 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___234_13854.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___234_13854.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13864 =
                        FStar_List.map (fun uu____13880  -> dummy) lbs2 in
                      FStar_List.append uu____13864 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13888 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13888 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___235_13904 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___235_13904.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___235_13904.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13931 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13931
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13950 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14026  ->
                        match uu____14026 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___236_14147 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___236_14147.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___236_14147.FStar_Syntax_Syntax.sort)
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
               (match uu____13950 with
                | (rec_env,memos,uu____14344) ->
                    let uu____14397 =
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
                             let uu____14928 =
                               let uu____14935 =
                                 let uu____14936 =
                                   let uu____14967 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14967, false) in
                                 Clos uu____14936 in
                               (FStar_Pervasives_Native.None, uu____14935) in
                             uu____14928 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15072 =
                      let uu____15073 = should_reify cfg stack1 in
                      Prims.op_Negation uu____15073 in
                    if uu____15072
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____15083 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15083
                        then
                          let uu___237_15084 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___237_15084.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___237_15084.primitive_steps);
                            strong = (uu___237_15084.strong)
                          }
                        else
                          (let uu___238_15086 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___238_15086.tcenv);
                             delta_level = (uu___238_15086.delta_level);
                             primitive_steps =
                               (uu___238_15086.primitive_steps);
                             strong = (uu___238_15086.strong)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____15088 =
                         let uu____15089 = FStar_Syntax_Subst.compress head1 in
                         uu____15089.FStar_Syntax_Syntax.n in
                       match uu____15088 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15107 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15107 with
                            | (uu____15108,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15114 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15122 =
                                         let uu____15123 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15123.FStar_Syntax_Syntax.n in
                                       match uu____15122 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15129,uu____15130))
                                           ->
                                           let uu____15139 =
                                             let uu____15140 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15140.FStar_Syntax_Syntax.n in
                                           (match uu____15139 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15146,msrc,uu____15148))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15157 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15157
                                            | uu____15158 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15159 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15160 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15160 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___239_15165 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___239_15165.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___239_15165.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___239_15165.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15166 =
                                            FStar_List.tl stack1 in
                                          let uu____15167 =
                                            let uu____15168 =
                                              let uu____15171 =
                                                let uu____15172 =
                                                  let uu____15185 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15185) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15172 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15171 in
                                            uu____15168
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15166
                                            uu____15167
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15201 =
                                            let uu____15202 = is_return body in
                                            match uu____15202 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15206;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15207;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15212 -> false in
                                          if uu____15201
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
                                               let uu____15236 =
                                                 let uu____15239 =
                                                   let uu____15240 =
                                                     let uu____15257 =
                                                       let uu____15260 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15260] in
                                                     (uu____15257, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15240 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15239 in
                                               uu____15236
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15276 =
                                                 let uu____15277 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15277.FStar_Syntax_Syntax.n in
                                               match uu____15276 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15283::uu____15284::[])
                                                   ->
                                                   let uu____15291 =
                                                     let uu____15294 =
                                                       let uu____15295 =
                                                         let uu____15302 =
                                                           let uu____15305 =
                                                             let uu____15306
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15306 in
                                                           let uu____15307 =
                                                             let uu____15310
                                                               =
                                                               let uu____15311
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15311 in
                                                             [uu____15310] in
                                                           uu____15305 ::
                                                             uu____15307 in
                                                         (bind1, uu____15302) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15295 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15294 in
                                                   uu____15291
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15319 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15325 =
                                                 let uu____15328 =
                                                   let uu____15329 =
                                                     let uu____15344 =
                                                       let uu____15347 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15348 =
                                                         let uu____15351 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15352 =
                                                           let uu____15355 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15356 =
                                                             let uu____15359
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15360
                                                               =
                                                               let uu____15363
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15364
                                                                 =
                                                                 let uu____15367
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15367] in
                                                               uu____15363 ::
                                                                 uu____15364 in
                                                             uu____15359 ::
                                                               uu____15360 in
                                                           uu____15355 ::
                                                             uu____15356 in
                                                         uu____15351 ::
                                                           uu____15352 in
                                                       uu____15347 ::
                                                         uu____15348 in
                                                     (bind_inst, uu____15344) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15329 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15328 in
                                               uu____15325
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15375 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15375 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15399 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15399 with
                            | (uu____15400,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15435 =
                                        let uu____15436 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15436.FStar_Syntax_Syntax.n in
                                      match uu____15435 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15442) -> t4
                                      | uu____15447 -> head2 in
                                    let uu____15448 =
                                      let uu____15449 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15449.FStar_Syntax_Syntax.n in
                                    match uu____15448 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15455 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15456 = maybe_extract_fv head2 in
                                  match uu____15456 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15466 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15466
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15471 =
                                          maybe_extract_fv head3 in
                                        match uu____15471 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15476 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15477 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15482 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15497 =
                                    match uu____15497 with
                                    | (e,q) ->
                                        let uu____15504 =
                                          let uu____15505 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15505.FStar_Syntax_Syntax.n in
                                        (match uu____15504 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15520 -> false) in
                                  let uu____15521 =
                                    let uu____15522 =
                                      let uu____15529 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15529 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15522 in
                                  if uu____15521
                                  then
                                    let uu____15534 =
                                      let uu____15535 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15535 in
                                    failwith uu____15534
                                  else ());
                                 (let uu____15537 =
                                    maybe_unfold_action head_app in
                                  match uu____15537 with
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
                                      let uu____15576 = FStar_List.tl stack1 in
                                      norm cfg env uu____15576 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15590 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15590 in
                           let uu____15591 = FStar_List.tl stack1 in
                           norm cfg env uu____15591 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15712  ->
                                     match uu____15712 with
                                     | (pat,wopt,tm) ->
                                         let uu____15760 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15760))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____15792 = FStar_List.tl stack1 in
                           norm cfg env uu____15792 tm
                       | uu____15793 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____15801 = should_reify cfg stack1 in
                    if uu____15801
                    then
                      let uu____15802 = FStar_List.tl stack1 in
                      let uu____15803 =
                        let uu____15804 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____15804 in
                      norm cfg env uu____15802 uu____15803
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____15807 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____15807
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___240_15816 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___240_15816.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___240_15816.primitive_steps);
                             strong = (uu___240_15816.strong)
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
                | uu____15818 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____15820::uu____15821 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____15826) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____15827 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____15858 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____15872 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____15872
                             | uu____15883 -> m in
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
              let uu____15895 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15895 in
            let uu____15896 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15896 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15909  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15920  ->
                      let uu____15921 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15922 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15921
                        uu____15922);
                 (let t1 =
                    let uu____15924 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____15924
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
                    | (UnivArgs (us',uu____15934))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____15989 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____15992 ->
                        let uu____15995 =
                          let uu____15996 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15996 in
                        failwith uu____15995
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
              let uu____16006 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16006 with
              | (uu____16007,return_repr) ->
                  let return_inst =
                    let uu____16016 =
                      let uu____16017 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16017.FStar_Syntax_Syntax.n in
                    match uu____16016 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16023::[]) ->
                        let uu____16030 =
                          let uu____16033 =
                            let uu____16034 =
                              let uu____16041 =
                                let uu____16044 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16044] in
                              (return_tm, uu____16041) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16034 in
                          FStar_Syntax_Syntax.mk uu____16033 in
                        uu____16030 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16052 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16055 =
                    let uu____16058 =
                      let uu____16059 =
                        let uu____16074 =
                          let uu____16077 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16078 =
                            let uu____16081 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16081] in
                          uu____16077 :: uu____16078 in
                        (return_inst, uu____16074) in
                      FStar_Syntax_Syntax.Tm_app uu____16059 in
                    FStar_Syntax_Syntax.mk uu____16058 in
                  uu____16055 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16090 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16090 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16093 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16093
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16094;
                     FStar_TypeChecker_Env.mtarget = uu____16095;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16096;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16107;
                     FStar_TypeChecker_Env.mtarget = uu____16108;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16109;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16127 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16127)
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
                (fun uu____16183  ->
                   match uu____16183 with
                   | (a,imp) ->
                       let uu____16194 = norm cfg env [] a in
                       (uu____16194, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___241_16211 = comp1 in
            let uu____16214 =
              let uu____16215 =
                let uu____16224 = norm cfg env [] t in
                let uu____16225 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16224, uu____16225) in
              FStar_Syntax_Syntax.Total uu____16215 in
            {
              FStar_Syntax_Syntax.n = uu____16214;
              FStar_Syntax_Syntax.pos =
                (uu___241_16211.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___241_16211.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___242_16240 = comp1 in
            let uu____16243 =
              let uu____16244 =
                let uu____16253 = norm cfg env [] t in
                let uu____16254 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16253, uu____16254) in
              FStar_Syntax_Syntax.GTotal uu____16244 in
            {
              FStar_Syntax_Syntax.n = uu____16243;
              FStar_Syntax_Syntax.pos =
                (uu___242_16240.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___242_16240.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16306  ->
                      match uu____16306 with
                      | (a,i) ->
                          let uu____16317 = norm cfg env [] a in
                          (uu____16317, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___191_16328  ->
                      match uu___191_16328 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16332 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16332
                      | f -> f)) in
            let uu___243_16336 = comp1 in
            let uu____16339 =
              let uu____16340 =
                let uu___244_16341 = ct in
                let uu____16342 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16343 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16346 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16342;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___244_16341.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16343;
                  FStar_Syntax_Syntax.effect_args = uu____16346;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16340 in
            {
              FStar_Syntax_Syntax.n = uu____16339;
              FStar_Syntax_Syntax.pos =
                (uu___243_16336.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___243_16336.FStar_Syntax_Syntax.vars)
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
            (let uu___245_16364 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___245_16364.tcenv);
               delta_level = (uu___245_16364.delta_level);
               primitive_steps = (uu___245_16364.primitive_steps);
               strong = (uu___245_16364.strong)
             }) env [] t in
        let non_info t =
          let uu____16369 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16369 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16372 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___246_16391 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___246_16391.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___246_16391.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16398 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16398
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
                    let uu___247_16409 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___247_16409.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___247_16409.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___247_16409.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___248_16411 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___248_16411.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___248_16411.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___248_16411.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___248_16411.FStar_Syntax_Syntax.flags)
                    } in
              let uu___249_16412 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___249_16412.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___249_16412.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16414 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16417  ->
        match uu____16417 with
        | (x,imp) ->
            let uu____16420 =
              let uu___250_16421 = x in
              let uu____16422 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___250_16421.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___250_16421.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16422
              } in
            (uu____16420, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16428 =
          FStar_List.fold_left
            (fun uu____16446  ->
               fun b  ->
                 match uu____16446 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16428 with | (nbs,uu____16486) -> FStar_List.rev nbs
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
            let uu____16502 =
              let uu___251_16503 = rc in
              let uu____16504 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___251_16503.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16504;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___251_16503.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16502
        | uu____16511 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16524  ->
               let uu____16525 = FStar_Syntax_Print.tag_of_term t in
               let uu____16526 = FStar_Syntax_Print.term_to_string t in
               let uu____16527 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16534 =
                 let uu____16535 =
                   let uu____16538 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16538 in
                 stack_to_string uu____16535 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16525 uu____16526 uu____16527 uu____16534);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16567 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16567
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16569 =
                     let uu____16570 =
                       let uu____16571 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16571 in
                     FStar_Util.string_of_int uu____16570 in
                   let uu____16576 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16577 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16569 uu____16576 uu____16577
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___252_16595 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___252_16595.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___252_16595.strong)
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16636  ->
                     let uu____16637 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16637);
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
               let uu____16673 =
                 let uu___253_16674 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___253_16674.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___253_16674.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16673
           | (Arg (Univ uu____16675,uu____16676,uu____16677))::uu____16678 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16681,uu____16682))::uu____16683 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16699),aq,r))::stack2 ->
               (log cfg
                  (fun uu____16752  ->
                     let uu____16753 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16753);
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
                  (let uu____16763 = FStar_ST.op_Bang m in
                   match uu____16763 with
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
                   | FStar_Pervasives_Native.Some (uu____16907,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16950 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____16950
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____16962  ->
                     let uu____16963 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16963);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16968 =
                   log cfg
                     (fun uu____16973  ->
                        let uu____16974 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16975 =
                          let uu____16976 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16993  ->
                                    match uu____16993 with
                                    | (p,uu____17003,uu____17004) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16976
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16974 uu____16975);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___192_17021  ->
                                match uu___192_17021 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17022 -> false)) in
                      let steps' =
                        let uu____17026 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____17026
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      let uu___254_17030 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___254_17030.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___254_17030.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17062 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17083 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17143  ->
                                    fun uu____17144  ->
                                      match (uu____17143, uu____17144) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17235 = norm_pat env3 p1 in
                                          (match uu____17235 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17083 with
                           | (pats1,env3) ->
                               ((let uu___255_17317 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___255_17317.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___256_17336 = x in
                            let uu____17337 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___256_17336.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___256_17336.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17337
                            } in
                          ((let uu___257_17351 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___257_17351.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___258_17362 = x in
                            let uu____17363 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___258_17362.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___258_17362.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17363
                            } in
                          ((let uu___259_17377 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___259_17377.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___260_17393 = x in
                            let uu____17394 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___260_17393.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___260_17393.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17394
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___261_17401 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___261_17401.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17411 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17425 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17425 with
                                  | (p,wopt,e) ->
                                      let uu____17445 = norm_pat env1 p in
                                      (match uu____17445 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17470 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17470 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17476 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17476) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17486) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17491 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17492;
                         FStar_Syntax_Syntax.fv_delta = uu____17493;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17494;
                         FStar_Syntax_Syntax.fv_delta = uu____17495;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17496);_}
                       -> true
                   | uu____17503 -> false in
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
                   let uu____17648 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17648 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17735 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____17774 ->
                                 let uu____17775 =
                                   let uu____17776 = is_cons head1 in
                                   Prims.op_Negation uu____17776 in
                                 FStar_Util.Inr uu____17775)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17801 =
                              let uu____17802 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17802.FStar_Syntax_Syntax.n in
                            (match uu____17801 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17820 ->
                                 let uu____17821 =
                                   let uu____17822 = is_cons head1 in
                                   Prims.op_Negation uu____17822 in
                                 FStar_Util.Inr uu____17821))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17891)::rest_a,(p1,uu____17894)::rest_p) ->
                       let uu____17938 = matches_pat t1 p1 in
                       (match uu____17938 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17987 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18093 = matches_pat scrutinee1 p1 in
                       (match uu____18093 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18133  ->
                                  let uu____18134 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18135 =
                                    let uu____18136 =
                                      FStar_List.map
                                        (fun uu____18146  ->
                                           match uu____18146 with
                                           | (uu____18151,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18136
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18134 uu____18135);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18182  ->
                                       match uu____18182 with
                                       | (bv,t1) ->
                                           let uu____18205 =
                                             let uu____18212 =
                                               let uu____18215 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18215 in
                                             let uu____18216 =
                                               let uu____18217 =
                                                 let uu____18248 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18248, false) in
                                               Clos uu____18217 in
                                             (uu____18212, uu____18216) in
                                           uu____18205 :: env2) env1 s in
                              let uu____18357 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18357))) in
                 let uu____18358 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18358
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___193_18381  ->
                match uu___193_18381 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18385 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18391 -> d in
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
            let uu___262_18420 = config s e in
            {
              steps = (uu___262_18420.steps);
              tcenv = (uu___262_18420.tcenv);
              delta_level = (uu___262_18420.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___262_18420.strong)
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
      fun t  -> let uu____18451 = config s e in norm_comp uu____18451 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18466 = config [] env in norm_universe uu____18466 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18481 = config [] env in ghost_to_pure_aux uu____18481 [] c
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
        let uu____18501 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18501 in
      let uu____18508 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18508
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___263_18510 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___263_18510.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___263_18510.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18513  ->
                    let uu____18514 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18514))
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
            ((let uu____18533 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18533);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18546 = config [AllowUnboundUniverses] env in
          norm_comp uu____18546 [] c
        with
        | e ->
            ((let uu____18559 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18559);
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
                   let uu____18599 =
                     let uu____18600 =
                       let uu____18607 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18607) in
                     FStar_Syntax_Syntax.Tm_refine uu____18600 in
                   mk uu____18599 t01.FStar_Syntax_Syntax.pos
               | uu____18612 -> t2)
          | uu____18613 -> t2 in
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
        let uu____18665 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18665 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18694 ->
                 let uu____18701 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18701 with
                  | (actuals,uu____18711,uu____18712) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18726 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18726 with
                         | (binders,args) ->
                             let uu____18743 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18743
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
      | uu____18753 ->
          let uu____18754 = FStar_Syntax_Util.head_and_args t in
          (match uu____18754 with
           | (head1,args) ->
               let uu____18791 =
                 let uu____18792 = FStar_Syntax_Subst.compress head1 in
                 uu____18792.FStar_Syntax_Syntax.n in
               (match uu____18791 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18795,thead) ->
                    let uu____18821 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18821 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18863 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___268_18871 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___268_18871.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___268_18871.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___268_18871.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___268_18871.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___268_18871.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___268_18871.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___268_18871.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___268_18871.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___268_18871.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___268_18871.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___268_18871.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___268_18871.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___268_18871.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___268_18871.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___268_18871.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___268_18871.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___268_18871.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___268_18871.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___268_18871.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___268_18871.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___268_18871.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___268_18871.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___268_18871.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___268_18871.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___268_18871.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___268_18871.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___268_18871.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___268_18871.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___268_18871.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___268_18871.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____18863 with
                            | (uu____18872,ty,uu____18874) ->
                                eta_expand_with_type env t ty))
                | uu____18875 ->
                    let uu____18876 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___269_18884 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___269_18884.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___269_18884.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___269_18884.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___269_18884.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___269_18884.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___269_18884.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___269_18884.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___269_18884.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___269_18884.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___269_18884.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___269_18884.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___269_18884.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___269_18884.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___269_18884.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___269_18884.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___269_18884.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___269_18884.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___269_18884.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___269_18884.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___269_18884.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___269_18884.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___269_18884.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___269_18884.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___269_18884.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___269_18884.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___269_18884.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___269_18884.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___269_18884.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___269_18884.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___269_18884.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____18876 with
                     | (uu____18885,ty,uu____18887) ->
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
            | (uu____18965,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18971,FStar_Util.Inl t) ->
                let uu____18977 =
                  let uu____18980 =
                    let uu____18981 =
                      let uu____18994 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18994) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18981 in
                  FStar_Syntax_Syntax.mk uu____18980 in
                uu____18977 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18998 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18998 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19025 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19080 ->
                    let uu____19081 =
                      let uu____19090 =
                        let uu____19091 = FStar_Syntax_Subst.compress t3 in
                        uu____19091.FStar_Syntax_Syntax.n in
                      (uu____19090, tc) in
                    (match uu____19081 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19116) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19153) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19192,FStar_Util.Inl uu____19193) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19216 -> failwith "Impossible") in
              (match uu____19025 with
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
          let uu____19325 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19325 with
          | (univ_names1,binders1,tc) ->
              let uu____19383 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19383)
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
          let uu____19422 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19422 with
          | (univ_names1,binders1,tc) ->
              let uu____19482 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19482)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19517 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19517 with
           | (univ_names1,binders1,typ1) ->
               let uu___270_19545 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___270_19545.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___270_19545.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___270_19545.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___270_19545.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___271_19566 = s in
          let uu____19567 =
            let uu____19568 =
              let uu____19577 = FStar_List.map (elim_uvars env) sigs in
              (uu____19577, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19568 in
          {
            FStar_Syntax_Syntax.sigel = uu____19567;
            FStar_Syntax_Syntax.sigrng =
              (uu___271_19566.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___271_19566.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___271_19566.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___271_19566.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19594 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19594 with
           | (univ_names1,uu____19612,typ1) ->
               let uu___272_19626 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___272_19626.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___272_19626.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___272_19626.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___272_19626.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19632 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19632 with
           | (univ_names1,uu____19650,typ1) ->
               let uu___273_19664 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___273_19664.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___273_19664.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___273_19664.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___273_19664.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19698 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19698 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19721 =
                            let uu____19722 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19722 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19721 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___274_19725 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___274_19725.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___274_19725.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___275_19726 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___275_19726.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___275_19726.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___275_19726.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___275_19726.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___276_19738 = s in
          let uu____19739 =
            let uu____19740 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19740 in
          {
            FStar_Syntax_Syntax.sigel = uu____19739;
            FStar_Syntax_Syntax.sigrng =
              (uu___276_19738.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___276_19738.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___276_19738.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___276_19738.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19744 = elim_uvars_aux_t env us [] t in
          (match uu____19744 with
           | (us1,uu____19762,t1) ->
               let uu___277_19776 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___277_19776.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___277_19776.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___277_19776.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___277_19776.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19777 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19779 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19779 with
           | (univs1,binders,signature) ->
               let uu____19807 =
                 let uu____19816 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19816 with
                 | (univs_opening,univs2) ->
                     let uu____19843 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19843) in
               (match uu____19807 with
                | (univs_opening,univs_closing) ->
                    let uu____19860 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19866 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19867 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19866, uu____19867) in
                    (match uu____19860 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19889 =
                           match uu____19889 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19907 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19907 with
                                | (us1,t1) ->
                                    let uu____19918 =
                                      let uu____19923 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19930 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19923, uu____19930) in
                                    (match uu____19918 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19943 =
                                           let uu____19948 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19957 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19948, uu____19957) in
                                         (match uu____19943 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19973 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19973 in
                                              let uu____19974 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19974 with
                                               | (uu____19995,uu____19996,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20011 =
                                                       let uu____20012 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20012 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20011 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20017 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20017 with
                           | (uu____20030,uu____20031,t1) -> t1 in
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
                             | uu____20091 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20108 =
                               let uu____20109 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20109.FStar_Syntax_Syntax.n in
                             match uu____20108 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20168 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20197 =
                               let uu____20198 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20198.FStar_Syntax_Syntax.n in
                             match uu____20197 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20219) ->
                                 let uu____20240 = destruct_action_body body in
                                 (match uu____20240 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20285 ->
                                 let uu____20286 = destruct_action_body t in
                                 (match uu____20286 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20335 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20335 with
                           | (action_univs,t) ->
                               let uu____20344 = destruct_action_typ_templ t in
                               (match uu____20344 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___278_20385 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___278_20385.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___278_20385.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___279_20387 = ed in
                           let uu____20388 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20389 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20390 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20391 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20392 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20393 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20394 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20395 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20396 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20397 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20398 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20399 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20400 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20401 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___279_20387.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___279_20387.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20388;
                             FStar_Syntax_Syntax.bind_wp = uu____20389;
                             FStar_Syntax_Syntax.if_then_else = uu____20390;
                             FStar_Syntax_Syntax.ite_wp = uu____20391;
                             FStar_Syntax_Syntax.stronger = uu____20392;
                             FStar_Syntax_Syntax.close_wp = uu____20393;
                             FStar_Syntax_Syntax.assert_p = uu____20394;
                             FStar_Syntax_Syntax.assume_p = uu____20395;
                             FStar_Syntax_Syntax.null_wp = uu____20396;
                             FStar_Syntax_Syntax.trivial = uu____20397;
                             FStar_Syntax_Syntax.repr = uu____20398;
                             FStar_Syntax_Syntax.return_repr = uu____20399;
                             FStar_Syntax_Syntax.bind_repr = uu____20400;
                             FStar_Syntax_Syntax.actions = uu____20401
                           } in
                         let uu___280_20404 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___280_20404.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___280_20404.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___280_20404.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___280_20404.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___194_20421 =
            match uu___194_20421 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20448 = elim_uvars_aux_t env us [] t in
                (match uu____20448 with
                 | (us1,uu____20472,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___281_20491 = sub_eff in
            let uu____20492 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20495 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___281_20491.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___281_20491.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20492;
              FStar_Syntax_Syntax.lift = uu____20495
            } in
          let uu___282_20498 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___282_20498.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___282_20498.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___282_20498.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___282_20498.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20508 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20508 with
           | (univ_names1,binders1,comp1) ->
               let uu___283_20542 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_20542.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_20542.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_20542.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_20542.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20553 -> s