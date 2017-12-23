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
  | Cfg of cfg
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____784 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____820 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____856 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____925 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____967 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1023 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1063 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1095 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1131 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1147 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1172 .
    'Auu____1172 ->
      FStar_Range.range -> 'Auu____1172 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1232 = FStar_ST.op_Bang r in
      match uu____1232 with
      | FStar_Pervasives_Native.Some uu____1309 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1391 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1391 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___72_1398  ->
    match uu___72_1398 with
    | Arg (c,uu____1400,uu____1401) ->
        let uu____1402 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1402
    | MemoLazy uu____1403 -> "MemoLazy"
    | Abs (uu____1410,bs,uu____1412,uu____1413,uu____1414) ->
        let uu____1419 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1419
    | UnivArgs uu____1424 -> "UnivArgs"
    | Match uu____1431 -> "Match"
    | App (uu____1438,t,uu____1440,uu____1441) ->
        let uu____1442 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1442
    | Meta (m,uu____1444) -> "Meta"
    | Let uu____1445 -> "Let"
    | Cfg uu____1454 -> "Cfg"
    | Debug (t,uu____1456) ->
        let uu____1457 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1457
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1465 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1465 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1481 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1481 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1494 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1494 then f () else ()
let is_empty: 'Auu____1498 . 'Auu____1498 Prims.list -> Prims.bool =
  fun uu___73_1504  ->
    match uu___73_1504 with | [] -> true | uu____1507 -> false
let lookup_bvar:
  'Auu____1514 'Auu____1515 .
    ('Auu____1515,'Auu____1514) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1514
  =
  fun env  ->
    fun x  ->
      try
        let uu____1539 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1539
      with
      | uu____1552 ->
          let uu____1553 =
            let uu____1554 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1554 in
          failwith uu____1553
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
          let uu____1591 =
            FStar_List.fold_left
              (fun uu____1617  ->
                 fun u1  ->
                   match uu____1617 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1642 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1642 with
                        | (k_u,n1) ->
                            let uu____1657 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1657
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1591 with
          | (uu____1675,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1700 =
                   let uu____1701 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1701 in
                 match uu____1700 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1719 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1728 ->
                   let uu____1729 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1729
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1735 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1744 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1753 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1760 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1760 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1777 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1777 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1785 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1793 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1793 with
                                  | (uu____1798,m) -> n1 <= m)) in
                        if uu____1785 then rest1 else us1
                    | uu____1803 -> us1)
               | uu____1808 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1812 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1812 in
        let uu____1815 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1815
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1817 = aux u in
           match uu____1817 with
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
          (fun uu____1921  ->
             let uu____1922 = FStar_Syntax_Print.tag_of_term t in
             let uu____1923 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1922
               uu____1923);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1930 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1932 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1957 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1958 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1959 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1960 ->
                  let uu____1977 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1977
                  then
                    let uu____1978 =
                      let uu____1979 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1980 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1979 uu____1980 in
                    failwith uu____1978
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1983 =
                    let uu____1984 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1984 in
                  mk uu____1983 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1991 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1991
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1993 = lookup_bvar env x in
                  (match uu____1993 with
                   | Univ uu____1996 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2000) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2112 = closures_as_binders_delayed cfg env bs in
                  (match uu____2112 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2140 =
                         let uu____2141 =
                           let uu____2158 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2158) in
                         FStar_Syntax_Syntax.Tm_abs uu____2141 in
                       mk uu____2140 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2189 = closures_as_binders_delayed cfg env bs in
                  (match uu____2189 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2231 =
                    let uu____2242 =
                      let uu____2249 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2249] in
                    closures_as_binders_delayed cfg env uu____2242 in
                  (match uu____2231 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2267 =
                         let uu____2268 =
                           let uu____2275 =
                             let uu____2276 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2276
                               FStar_Pervasives_Native.fst in
                           (uu____2275, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2268 in
                       mk uu____2267 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2367 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2367
                    | FStar_Util.Inr c ->
                        let uu____2381 = close_comp cfg env c in
                        FStar_Util.Inr uu____2381 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2397 =
                    let uu____2398 =
                      let uu____2425 = closure_as_term_delayed cfg env t11 in
                      (uu____2425, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2398 in
                  mk uu____2397 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2476 =
                    let uu____2477 =
                      let uu____2484 = closure_as_term_delayed cfg env t' in
                      let uu____2487 =
                        let uu____2488 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2488 in
                      (uu____2484, uu____2487) in
                    FStar_Syntax_Syntax.Tm_meta uu____2477 in
                  mk uu____2476 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2548 =
                    let uu____2549 =
                      let uu____2556 = closure_as_term_delayed cfg env t' in
                      let uu____2559 =
                        let uu____2560 =
                          let uu____2567 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2567) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2560 in
                      (uu____2556, uu____2559) in
                    FStar_Syntax_Syntax.Tm_meta uu____2549 in
                  mk uu____2548 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2586 =
                    let uu____2587 =
                      let uu____2594 = closure_as_term_delayed cfg env t' in
                      let uu____2597 =
                        let uu____2598 =
                          let uu____2607 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2607) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2598 in
                      (uu____2594, uu____2597) in
                    FStar_Syntax_Syntax.Tm_meta uu____2587 in
                  mk uu____2586 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2620 =
                    let uu____2621 =
                      let uu____2628 = closure_as_term_delayed cfg env t' in
                      (uu____2628, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2621 in
                  mk uu____2620 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2668  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2687 =
                    let uu____2698 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2698
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2717 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___92_2729 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___92_2729.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___92_2729.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2717)) in
                  (match uu____2687 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___93_2745 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___93_2745.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___93_2745.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2756,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2815  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2840 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2840
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2860  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2882 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2882
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___94_2894 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___94_2894.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___94_2894.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___95_2895 = lb in
                    let uu____2896 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___95_2895.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___95_2895.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2896
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2926  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3015 =
                    match uu____3015 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3070 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3091 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3151  ->
                                        fun uu____3152  ->
                                          match (uu____3151, uu____3152) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3243 =
                                                norm_pat env3 p1 in
                                              (match uu____3243 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3091 with
                               | (pats1,env3) ->
                                   ((let uu___96_3325 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___96_3325.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___97_3344 = x in
                                let uu____3345 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___97_3344.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___97_3344.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3345
                                } in
                              ((let uu___98_3359 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___98_3359.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___99_3370 = x in
                                let uu____3371 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___99_3370.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___99_3370.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3371
                                } in
                              ((let uu___100_3385 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___100_3385.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___101_3401 = x in
                                let uu____3402 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___101_3401.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___101_3401.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3402
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___102_3409 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___102_3409.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3412 = norm_pat env1 pat in
                        (match uu____3412 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3441 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3441 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3447 =
                    let uu____3448 =
                      let uu____3471 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3471) in
                    FStar_Syntax_Syntax.Tm_match uu____3448 in
                  mk uu____3447 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3557 -> closure_as_term cfg env t
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
        | uu____3583 ->
            FStar_List.map
              (fun uu____3600  ->
                 match uu____3600 with
                 | (x,imp) ->
                     let uu____3619 = closure_as_term_delayed cfg env x in
                     (uu____3619, imp)) args
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
        let uu____3633 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3682  ->
                  fun uu____3683  ->
                    match (uu____3682, uu____3683) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___103_3753 = b in
                          let uu____3754 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___103_3753.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___103_3753.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3754
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3633 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3847 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3860 = closure_as_term_delayed cfg env t in
                 let uu____3861 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3860 uu____3861
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3874 = closure_as_term_delayed cfg env t in
                 let uu____3875 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3874 uu____3875
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
                        (fun uu___74_3901  ->
                           match uu___74_3901 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3905 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3905
                           | f -> f)) in
                 let uu____3909 =
                   let uu___104_3910 = c1 in
                   let uu____3911 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3911;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___104_3910.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3909)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___75_3921  ->
            match uu___75_3921 with
            | FStar_Syntax_Syntax.DECREASES uu____3922 -> false
            | uu____3925 -> true))
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
                   (fun uu___76_3943  ->
                      match uu___76_3943 with
                      | FStar_Syntax_Syntax.DECREASES uu____3944 -> false
                      | uu____3947 -> true)) in
            let rc1 =
              let uu___105_3949 = rc in
              let uu____3950 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___105_3949.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3950;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3957 -> lopt
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
    let uu____4047 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4047 in
  let arg_as_bounded_int uu____4075 =
    match uu____4075 with
    | (a,uu____4087) ->
        let uu____4094 =
          let uu____4095 = FStar_Syntax_Subst.compress a in
          uu____4095.FStar_Syntax_Syntax.n in
        (match uu____4094 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4105;
                FStar_Syntax_Syntax.vars = uu____4106;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4108;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4109;_},uu____4110)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4149 =
               let uu____4154 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4154) in
             FStar_Pervasives_Native.Some uu____4149
         | uu____4159 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4201 = f a in FStar_Pervasives_Native.Some uu____4201
    | uu____4202 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4252 = f a0 a1 in FStar_Pervasives_Native.Some uu____4252
    | uu____4253 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4302 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4302 in
  let binary_op as_a f res args =
    let uu____4358 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4358 in
  let as_primitive_step uu____4382 =
    match uu____4382 with
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
           let uu____4430 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4430) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4458 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4458) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4479 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4479) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4507 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4507) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4535 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4535) in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4652 =
          let uu____4661 = as_a a in
          let uu____4664 = as_b b in (uu____4661, uu____4664) in
        (match uu____4652 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4679 =
               let uu____4680 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4680 in
             FStar_Pervasives_Native.Some uu____4679
         | uu____4681 -> FStar_Pervasives_Native.None)
    | uu____4690 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4704 =
        let uu____4705 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4705 in
      mk uu____4704 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4715 =
      let uu____4718 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4718 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4715 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4750 =
      let uu____4751 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4751 in
    FStar_Syntax_Embeddings.embed_int rng uu____4750 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4769 = arg_as_string a1 in
        (match uu____4769 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4775 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4775 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4788 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4788
              | uu____4789 -> FStar_Pervasives_Native.None)
         | uu____4794 -> FStar_Pervasives_Native.None)
    | uu____4797 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4807 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4807 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4831 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4842 =
          let uu____4863 = arg_as_string fn in
          let uu____4866 = arg_as_int from_line in
          let uu____4869 = arg_as_int from_col in
          let uu____4872 = arg_as_int to_line in
          let uu____4875 = arg_as_int to_col in
          (uu____4863, uu____4866, uu____4869, uu____4872, uu____4875) in
        (match uu____4842 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4906 =
                 let uu____4907 = FStar_BigInt.to_int_fs from_l in
                 let uu____4908 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4907 uu____4908 in
               let uu____4909 =
                 let uu____4910 = FStar_BigInt.to_int_fs to_l in
                 let uu____4911 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4910 uu____4911 in
               FStar_Range.mk_range fn1 uu____4906 uu____4909 in
             let uu____4912 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4912
         | uu____4917 -> FStar_Pervasives_Native.None)
    | uu____4938 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4965)::(a1,uu____4967)::(a2,uu____4969)::[] ->
        let uu____5006 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5006 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5019 -> FStar_Pervasives_Native.None)
    | uu____5020 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____5047)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5056 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5080 =
      let uu____5095 =
        let uu____5110 =
          let uu____5125 =
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
                                              let uu____5393 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5393,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5400 =
                                              let uu____5415 =
                                                let uu____5428 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5428,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5439 =
                                                let uu____5454 =
                                                  let uu____5469 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5469,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5478 =
                                                  let uu____5495 =
                                                    let uu____5510 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5510,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5519 =
                                                    let uu____5536 =
                                                      let uu____5555 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5555,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5536] in
                                                  uu____5495 :: uu____5519 in
                                                uu____5454 :: uu____5478 in
                                              uu____5415 :: uu____5439 in
                                            uu____5380 :: uu____5400 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5365 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5350 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5335 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5320 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5305 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5773 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5773 y)))
                                  :: uu____5290 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5275 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5260 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5245 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5230 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5215 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5919 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5919)))
                      :: uu____5200 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5945 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5945)))
                    :: uu____5185 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5971 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5971)))
                  :: uu____5170 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5997 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5997)))
                :: uu____5155 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5140 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5125 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5110 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5095 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5080 in
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
      let uu____6147 =
        let uu____6148 =
          let uu____6149 = FStar_Syntax_Syntax.as_arg c in [uu____6149] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6148 in
      uu____6147 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6184 =
              let uu____6197 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6197, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6217  ->
                        fun uu____6218  ->
                          match (uu____6217, uu____6218) with
                          | ((int_to_t1,x),(uu____6237,y)) ->
                              let uu____6247 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6247))) in
            let uu____6248 =
              let uu____6263 =
                let uu____6276 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6276, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6296  ->
                          fun uu____6297  ->
                            match (uu____6296, uu____6297) with
                            | ((int_to_t1,x),(uu____6316,y)) ->
                                let uu____6326 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6326))) in
              let uu____6327 =
                let uu____6342 =
                  let uu____6355 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6355, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6375  ->
                            fun uu____6376  ->
                              match (uu____6375, uu____6376) with
                              | ((int_to_t1,x),(uu____6395,y)) ->
                                  let uu____6405 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6405))) in
                [uu____6342] in
              uu____6263 :: uu____6327 in
            uu____6184 :: uu____6248)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6495)::(a1,uu____6497)::(a2,uu____6499)::[] ->
        let uu____6536 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6536 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6542 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6542.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6542.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6546 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6546.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6546.FStar_Syntax_Syntax.vars)
                })
         | uu____6547 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6549)::uu____6550::(a1,uu____6552)::(a2,uu____6554)::[] ->
        let uu____6603 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6603 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6609 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6609.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6609.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6613 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6613.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6613.FStar_Syntax_Syntax.vars)
                })
         | uu____6614 -> FStar_Pervasives_Native.None)
    | uu____6615 -> failwith "Unexpected number of arguments" in
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
      let uu____6634 =
        let uu____6635 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6635 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6634
    with | uu____6641 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6645 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6645) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6705  ->
           fun subst1  ->
             match uu____6705 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6747)) ->
                      let uu____6806 = b in
                      (match uu____6806 with
                       | (bv,uu____6814) ->
                           let uu____6815 =
                             let uu____6816 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6816 in
                           if uu____6815
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6821 = unembed_binder term1 in
                              match uu____6821 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6828 =
                                      let uu___110_6829 = bv in
                                      let uu____6830 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___110_6829.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___110_6829.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6830
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6828 in
                                  let b_for_x =
                                    let uu____6834 =
                                      let uu____6841 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6841) in
                                    FStar_Syntax_Syntax.NT uu____6834 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___77_6850  ->
                                         match uu___77_6850 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6851,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6853;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6854;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6859 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6860 -> subst1)) env []
let reduce_primops:
  'Auu____6877 'Auu____6878 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6878) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6877 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6919 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6919
          then tm
          else
            (let uu____6921 = FStar_Syntax_Util.head_and_args tm in
             match uu____6921 with
             | (head1,args) ->
                 let uu____6958 =
                   let uu____6959 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6959.FStar_Syntax_Syntax.n in
                 (match uu____6958 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6963 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6963 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6980  ->
                                   let uu____6981 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6982 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6989 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6981 uu____6982 uu____6989);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6994  ->
                                   let uu____6995 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6995);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6998  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7000 =
                                 prim_step.interpretation psc args in
                               match uu____7000 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7006  ->
                                         let uu____7007 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7007);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7013  ->
                                         let uu____7014 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7015 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7014 uu____7015);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7016 ->
                           (log_primops cfg
                              (fun uu____7020  ->
                                 let uu____7021 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7021);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7025  ->
                            let uu____7026 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7026);
                       (match args with
                        | (a1,uu____7028)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7045 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7057  ->
                            let uu____7058 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7058);
                       (match args with
                        | (t,uu____7060)::(r,uu____7062)::[] ->
                            let uu____7089 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7089 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___111_7093 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___111_7093.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___111_7093.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7096 -> tm))
                  | uu____7105 -> tm))
let reduce_equality:
  'Auu____7110 'Auu____7111 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7111) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7110 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___112_7149 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___112_7149.tcenv);
           delta_level = (uu___112_7149.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___112_7149.strong)
         }) tm
let maybe_simplify_aux:
  'Auu____7156 'Auu____7157 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7157) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7156 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7199 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7199
          then tm1
          else
            (let w t =
               let uu___113_7211 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___113_7211.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___113_7211.FStar_Syntax_Syntax.vars)
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
               | uu____7228 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7233 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7233
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7254 =
                 match uu____7254 with
                 | (t1,q) ->
                     let uu____7267 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7267 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7295 -> (t1, q)) in
               let uu____7304 = FStar_Syntax_Util.head_and_args t in
               match uu____7304 with
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
                         FStar_Syntax_Syntax.pos = uu____7401;
                         FStar_Syntax_Syntax.vars = uu____7402;_},uu____7403);
                    FStar_Syntax_Syntax.pos = uu____7404;
                    FStar_Syntax_Syntax.vars = uu____7405;_},args)
                 ->
                 let uu____7431 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7431
                 then
                   let uu____7432 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7432 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7487)::
                        (uu____7488,(arg,uu____7490))::[] ->
                        maybe_auto_squash arg
                    | (uu____7555,(arg,uu____7557))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7558)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7623)::uu____7624::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7687::(FStar_Pervasives_Native.Some (false
                                   ),uu____7688)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7751 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7767 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7767
                    then
                      let uu____7768 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7768 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7823)::uu____7824::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7887::(FStar_Pervasives_Native.Some (true
                                     ),uu____7888)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7951)::
                          (uu____7952,(arg,uu____7954))::[] ->
                          maybe_auto_squash arg
                      | (uu____8019,(arg,uu____8021))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8022)::[]
                          -> maybe_auto_squash arg
                      | uu____8087 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8103 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8103
                       then
                         let uu____8104 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8104 with
                         | uu____8159::(FStar_Pervasives_Native.Some (true
                                        ),uu____8160)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8223)::uu____8224::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8287)::
                             (uu____8288,(arg,uu____8290))::[] ->
                             maybe_auto_squash arg
                         | (uu____8355,(p,uu____8357))::(uu____8358,(q,uu____8360))::[]
                             ->
                             let uu____8425 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8425
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8427 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8443 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8443
                          then
                            let uu____8444 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8444 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8499)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8538)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8577 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8593 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8593
                             then
                               match args with
                               | (t,uu____8595)::[] ->
                                   let uu____8612 =
                                     let uu____8613 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8613.FStar_Syntax_Syntax.n in
                                   (match uu____8612 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8616::[],body,uu____8618) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8645 -> tm1)
                                    | uu____8648 -> tm1)
                               | (uu____8649,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8650))::
                                   (t,uu____8652)::[] ->
                                   let uu____8691 =
                                     let uu____8692 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8692.FStar_Syntax_Syntax.n in
                                   (match uu____8691 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8695::[],body,uu____8697) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8724 -> tm1)
                                    | uu____8727 -> tm1)
                               | uu____8728 -> tm1
                             else
                               (let uu____8738 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8738
                                then
                                  match args with
                                  | (t,uu____8740)::[] ->
                                      let uu____8757 =
                                        let uu____8758 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8758.FStar_Syntax_Syntax.n in
                                      (match uu____8757 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8761::[],body,uu____8763)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8790 -> tm1)
                                       | uu____8793 -> tm1)
                                  | (uu____8794,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8795))::(t,uu____8797)::[] ->
                                      let uu____8836 =
                                        let uu____8837 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8837.FStar_Syntax_Syntax.n in
                                      (match uu____8836 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8840::[],body,uu____8842)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8869 -> tm1)
                                       | uu____8872 -> tm1)
                                  | uu____8873 -> tm1
                                else
                                  (let uu____8883 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8883
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8884;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8885;_},uu____8886)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8903;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8904;_},uu____8905)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8922 -> tm1
                                   else
                                     (let uu____8932 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8932 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8952 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8962;
                    FStar_Syntax_Syntax.vars = uu____8963;_},args)
                 ->
                 let uu____8985 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8985
                 then
                   let uu____8986 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8986 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9041)::
                        (uu____9042,(arg,uu____9044))::[] ->
                        maybe_auto_squash arg
                    | (uu____9109,(arg,uu____9111))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9112)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9177)::uu____9178::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9241::(FStar_Pervasives_Native.Some (false
                                   ),uu____9242)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9305 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9321 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9321
                    then
                      let uu____9322 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9322 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9377)::uu____9378::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9441::(FStar_Pervasives_Native.Some (true
                                     ),uu____9442)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9505)::
                          (uu____9506,(arg,uu____9508))::[] ->
                          maybe_auto_squash arg
                      | (uu____9573,(arg,uu____9575))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9576)::[]
                          -> maybe_auto_squash arg
                      | uu____9641 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9657 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9657
                       then
                         let uu____9658 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9658 with
                         | uu____9713::(FStar_Pervasives_Native.Some (true
                                        ),uu____9714)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9777)::uu____9778::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9841)::
                             (uu____9842,(arg,uu____9844))::[] ->
                             maybe_auto_squash arg
                         | (uu____9909,(p,uu____9911))::(uu____9912,(q,uu____9914))::[]
                             ->
                             let uu____9979 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9979
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9981 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9997 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9997
                          then
                            let uu____9998 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9998 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10053)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10092)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10131 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10147 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10147
                             then
                               match args with
                               | (t,uu____10149)::[] ->
                                   let uu____10166 =
                                     let uu____10167 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10167.FStar_Syntax_Syntax.n in
                                   (match uu____10166 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10170::[],body,uu____10172) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10199 -> tm1)
                                    | uu____10202 -> tm1)
                               | (uu____10203,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10204))::
                                   (t,uu____10206)::[] ->
                                   let uu____10245 =
                                     let uu____10246 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10246.FStar_Syntax_Syntax.n in
                                   (match uu____10245 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10249::[],body,uu____10251) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10278 -> tm1)
                                    | uu____10281 -> tm1)
                               | uu____10282 -> tm1
                             else
                               (let uu____10292 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10292
                                then
                                  match args with
                                  | (t,uu____10294)::[] ->
                                      let uu____10311 =
                                        let uu____10312 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10312.FStar_Syntax_Syntax.n in
                                      (match uu____10311 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10315::[],body,uu____10317)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10344 -> tm1)
                                       | uu____10347 -> tm1)
                                  | (uu____10348,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10349))::(t,uu____10351)::[] ->
                                      let uu____10390 =
                                        let uu____10391 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10391.FStar_Syntax_Syntax.n in
                                      (match uu____10390 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10394::[],body,uu____10396)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10423 -> tm1)
                                       | uu____10426 -> tm1)
                                  | uu____10427 -> tm1
                                else
                                  (let uu____10437 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10437
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10438;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10439;_},uu____10440)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10457;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10458;_},uu____10459)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10476 -> tm1
                                   else
                                     (let uu____10486 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10486 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10506 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10515 -> tm1)
let maybe_simplify:
  'Auu____10522 'Auu____10523 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10523) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10522 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10566 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10566
           then
             let uu____10567 = FStar_Syntax_Print.term_to_string tm in
             let uu____10568 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10567 uu____10568
           else ());
          tm'
let is_norm_request:
  'Auu____10574 .
    FStar_Syntax_Syntax.term -> 'Auu____10574 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10587 =
        let uu____10594 =
          let uu____10595 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10595.FStar_Syntax_Syntax.n in
        (uu____10594, args) in
      match uu____10587 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10601::uu____10602::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10606::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10611::uu____10612::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10615 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___78_10626  ->
    match uu___78_10626 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10632 =
          let uu____10635 =
            let uu____10636 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10636 in
          [uu____10635] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10632
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10651 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10651) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10689 =
          let uu____10692 =
            let uu____10697 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10697 s in
          FStar_All.pipe_right uu____10692 FStar_Util.must in
        FStar_All.pipe_right uu____10689 tr_norm_steps in
      match args with
      | uu____10722::(tm,uu____10724)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10747)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10762)::uu____10763::(tm,uu____10765)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10805 =
              let uu____10808 = full_norm steps in parse_steps uu____10808 in
            Beta :: uu____10805 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10817 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___79_10834  ->
    match uu___79_10834 with
    | (App
        (uu____10837,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10838;
                       FStar_Syntax_Syntax.vars = uu____10839;_},uu____10840,uu____10841))::uu____10842
        -> true
    | uu____10849 -> false
let firstn:
  'Auu____10855 .
    Prims.int ->
      'Auu____10855 Prims.list ->
        ('Auu____10855 Prims.list,'Auu____10855 Prims.list)
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
          (uu____10891,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10892;
                         FStar_Syntax_Syntax.vars = uu____10893;_},uu____10894,uu____10895))::uu____10896
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10903 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11058  ->
               let uu____11059 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11060 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11061 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11068 =
                 let uu____11069 =
                   let uu____11072 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11072 in
                 stack_to_string uu____11069 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11059 uu____11060 uu____11061 uu____11068);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11095 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11120 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11137 =
                 let uu____11138 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11139 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11138 uu____11139 in
               failwith uu____11137
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11140 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11157 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11158 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11159;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11160;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11163;
                 FStar_Syntax_Syntax.fv_delta = uu____11164;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11165;
                 FStar_Syntax_Syntax.fv_delta = uu____11166;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11167);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11175 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11175 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11181  ->
                     let uu____11182 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11183 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11182 uu____11183);
                if b
                then
                  (let uu____11184 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11184 t1 fv)
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
                 let uu___114_11223 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___114_11223.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_11223.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11256 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11256) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___115_11264 = cfg in
                 let uu____11265 =
                   FStar_List.filter
                     (fun uu___80_11268  ->
                        match uu___80_11268 with
                        | UnfoldOnly uu____11269 -> false
                        | NoDeltaSteps  -> false
                        | uu____11272 -> true) cfg.steps in
                 {
                   steps = uu____11265;
                   tcenv = (uu___115_11264.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___115_11264.primitive_steps);
                   strong = (uu___115_11264.strong)
                 } in
               let uu____11273 = get_norm_request (norm cfg' env []) args in
               (match uu____11273 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11289 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___81_11294  ->
                                match uu___81_11294 with
                                | UnfoldUntil uu____11295 -> true
                                | UnfoldOnly uu____11296 -> true
                                | uu____11299 -> false)) in
                      if uu____11289
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___116_11304 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___116_11304.tcenv);
                        delta_level;
                        primitive_steps = (uu___116_11304.primitive_steps);
                        strong = (uu___116_11304.strong)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11311 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11311
                      then
                        let uu____11314 =
                          let uu____11315 =
                            let uu____11320 = FStar_Util.now () in
                            (t1, uu____11320) in
                          Debug uu____11315 in
                        uu____11314 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11324 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11324
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11331 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11331
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11334 =
                      let uu____11341 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11341, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11334 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___82_11354  ->
                         match uu___82_11354 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11357 =
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
                 if uu____11357
                 then false
                 else
                   (let uu____11359 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___83_11366  ->
                              match uu___83_11366 with
                              | UnfoldOnly uu____11367 -> true
                              | uu____11370 -> false)) in
                    match uu____11359 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11374 -> should_delta) in
               (log cfg
                  (fun uu____11382  ->
                     let uu____11383 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11384 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11385 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11383 uu____11384 uu____11385);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11388 = lookup_bvar env x in
               (match uu____11388 with
                | Univ uu____11391 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11440 = FStar_ST.op_Bang r in
                      (match uu____11440 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11587  ->
                                 let uu____11588 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11589 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11588
                                   uu____11589);
                            (let uu____11590 =
                               let uu____11591 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11591.FStar_Syntax_Syntax.n in
                             match uu____11590 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11594 ->
                                 norm cfg env2 stack t'
                             | uu____11611 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11681)::uu____11682 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11691)::uu____11692 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11702,uu____11703))::stack_rest ->
                    (match c with
                     | Univ uu____11707 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11716 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11737  ->
                                    let uu____11738 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11738);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11778  ->
                                    let uu____11779 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11779);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11857  ->
                          let uu____11858 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11858);
                     norm cfg env stack1 t1)
                | (Debug uu____11859)::uu____11860 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11867 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11867
                    else
                      (let uu____11869 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11869 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11911  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11939 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11939
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11949 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11949)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_11954 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_11954.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_11954.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11955 -> lopt in
                           (log cfg
                              (fun uu____11961  ->
                                 let uu____11962 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11962);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_11971 = cfg in
                               {
                                 steps = (uu___118_11971.steps);
                                 tcenv = (uu___118_11971.tcenv);
                                 delta_level = (uu___118_11971.delta_level);
                                 primitive_steps =
                                   (uu___118_11971.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11982)::uu____11983 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11990 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11990
                    else
                      (let uu____11992 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11992 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12034  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12062 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12062
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12072 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12072)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12077 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12077.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12077.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12078 -> lopt in
                           (log cfg
                              (fun uu____12084  ->
                                 let uu____12085 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12085);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12094 = cfg in
                               {
                                 steps = (uu___118_12094.steps);
                                 tcenv = (uu___118_12094.tcenv);
                                 delta_level = (uu___118_12094.delta_level);
                                 primitive_steps =
                                   (uu___118_12094.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12105)::uu____12106 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12117 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12117
                    else
                      (let uu____12119 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12119 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12161  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12189 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12189
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12199 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12199)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12204 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12204.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12204.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12205 -> lopt in
                           (log cfg
                              (fun uu____12211  ->
                                 let uu____12212 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12212);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12221 = cfg in
                               {
                                 steps = (uu___118_12221.steps);
                                 tcenv = (uu___118_12221.tcenv);
                                 delta_level = (uu___118_12221.delta_level);
                                 primitive_steps =
                                   (uu___118_12221.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12232)::uu____12233 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12244 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12244
                    else
                      (let uu____12246 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12246 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12288  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12316 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12316
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12326 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12326)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12331 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12331.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12331.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12332 -> lopt in
                           (log cfg
                              (fun uu____12338  ->
                                 let uu____12339 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12339);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12348 = cfg in
                               {
                                 steps = (uu___118_12348.steps);
                                 tcenv = (uu___118_12348.tcenv);
                                 delta_level = (uu___118_12348.delta_level);
                                 primitive_steps =
                                   (uu___118_12348.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12359)::uu____12360 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12375 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12375
                    else
                      (let uu____12377 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12377 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12419  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12447 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12447
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12457 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12457)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12462 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12462.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12462.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12463 -> lopt in
                           (log cfg
                              (fun uu____12469  ->
                                 let uu____12470 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12470);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12479 = cfg in
                               {
                                 steps = (uu___118_12479.steps);
                                 tcenv = (uu___118_12479.tcenv);
                                 delta_level = (uu___118_12479.delta_level);
                                 primitive_steps =
                                   (uu___118_12479.primitive_steps);
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
                      let uu____12490 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12490
                    else
                      (let uu____12492 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12492 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12534  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12562 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12562
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12572 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12572)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___117_12577 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_12577.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_12577.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12578 -> lopt in
                           (log cfg
                              (fun uu____12584  ->
                                 let uu____12585 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12585);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___118_12594 = cfg in
                               {
                                 steps = (uu___118_12594.steps);
                                 tcenv = (uu___118_12594.tcenv);
                                 delta_level = (uu___118_12594.delta_level);
                                 primitive_steps =
                                   (uu___118_12594.primitive_steps);
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
                      (fun uu____12643  ->
                         fun stack1  ->
                           match uu____12643 with
                           | (a,aq) ->
                               let uu____12655 =
                                 let uu____12656 =
                                   let uu____12663 =
                                     let uu____12664 =
                                       let uu____12695 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12695, false) in
                                     Clos uu____12664 in
                                   (uu____12663, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12656 in
                               uu____12655 :: stack1) args) in
               (log cfg
                  (fun uu____12779  ->
                     let uu____12780 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12780);
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
                             ((let uu___119_12816 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___119_12816.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___119_12816.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12817 ->
                      let uu____12822 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12822)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12825 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12825 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12856 =
                          let uu____12857 =
                            let uu____12864 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___120_12866 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_12866.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_12866.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12864) in
                          FStar_Syntax_Syntax.Tm_refine uu____12857 in
                        mk uu____12856 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12885 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12885
               else
                 (let uu____12887 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12887 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12895 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12919  -> dummy :: env1) env) in
                        norm_comp cfg uu____12895 c1 in
                      let t2 =
                        let uu____12941 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12941 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13000)::uu____13001 ->
                    (log cfg
                       (fun uu____13012  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13013)::uu____13014 ->
                    (log cfg
                       (fun uu____13025  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13026,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13027;
                                   FStar_Syntax_Syntax.vars = uu____13028;_},uu____13029,uu____13030))::uu____13031
                    ->
                    (log cfg
                       (fun uu____13040  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13041)::uu____13042 ->
                    (log cfg
                       (fun uu____13053  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13054 ->
                    (log cfg
                       (fun uu____13057  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13061  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13078 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13078
                         | FStar_Util.Inr c ->
                             let uu____13086 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13086 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13099 =
                               let uu____13100 =
                                 let uu____13127 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13127, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13100 in
                             mk uu____13099 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13146 ->
                           let uu____13147 =
                             let uu____13148 =
                               let uu____13149 =
                                 let uu____13176 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13176, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13149 in
                             mk uu____13148 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13147))))
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
                         let uu____13286 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13286 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___121_13306 = cfg in
                               let uu____13307 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___121_13306.steps);
                                 tcenv = uu____13307;
                                 delta_level = (uu___121_13306.delta_level);
                                 primitive_steps =
                                   (uu___121_13306.primitive_steps);
                                 strong = (uu___121_13306.strong)
                               } in
                             let norm1 t2 =
                               let uu____13312 =
                                 let uu____13313 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13313 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13312 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___122_13316 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___122_13316.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___122_13316.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13317 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13317
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13328,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13329;
                               FStar_Syntax_Syntax.lbunivs = uu____13330;
                               FStar_Syntax_Syntax.lbtyp = uu____13331;
                               FStar_Syntax_Syntax.lbeff = uu____13332;
                               FStar_Syntax_Syntax.lbdef = uu____13333;_}::uu____13334),uu____13335)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13371 =
                 (let uu____13374 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13374) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13376 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13376))) in
               if uu____13371
               then
                 let binder =
                   let uu____13378 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13378 in
                 let env1 =
                   let uu____13388 =
                     let uu____13395 =
                       let uu____13396 =
                         let uu____13427 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13427,
                           false) in
                       Clos uu____13396 in
                     ((FStar_Pervasives_Native.Some binder), uu____13395) in
                   uu____13388 :: env in
                 (log cfg
                    (fun uu____13520  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13522 =
                    let uu____13527 =
                      let uu____13528 =
                        let uu____13529 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13529
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13528] in
                    FStar_Syntax_Subst.open_term uu____13527 body in
                  match uu____13522 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13538  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13546 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13546 in
                          FStar_Util.Inl
                            (let uu___123_13556 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_13556.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_13556.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13559  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___124_13561 = lb in
                           let uu____13562 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___124_13561.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___124_13561.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13562
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13597  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___125_13620 = cfg in
                           {
                             steps = (uu___125_13620.steps);
                             tcenv = (uu___125_13620.tcenv);
                             delta_level = (uu___125_13620.delta_level);
                             primitive_steps =
                               (uu___125_13620.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13623  ->
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
               let uu____13640 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13640 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13676 =
                               let uu___126_13677 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___126_13677.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___126_13677.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13676 in
                           let uu____13678 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13678 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13704 =
                                   FStar_List.map (fun uu____13720  -> dummy)
                                     lbs1 in
                                 let uu____13721 =
                                   let uu____13730 =
                                     FStar_List.map
                                       (fun uu____13750  -> dummy) xs1 in
                                   FStar_List.append uu____13730 env in
                                 FStar_List.append uu____13704 uu____13721 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13774 =
                                       let uu___127_13775 = rc in
                                       let uu____13776 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___127_13775.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13776;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___127_13775.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13774
                                 | uu____13783 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___128_13787 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___128_13787.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___128_13787.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13797 =
                        FStar_List.map (fun uu____13813  -> dummy) lbs2 in
                      FStar_List.append uu____13797 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13821 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13821 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___129_13837 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___129_13837.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___129_13837.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13864 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13864
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13883 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13959  ->
                        match uu____13959 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___130_14080 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___130_14080.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___130_14080.FStar_Syntax_Syntax.sort)
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
               (match uu____13883 with
                | (rec_env,memos,uu____14293) ->
                    let uu____14346 =
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
                             let uu____14889 =
                               let uu____14896 =
                                 let uu____14897 =
                                   let uu____14928 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14928, false) in
                                 Clos uu____14897 in
                               (FStar_Pervasives_Native.None, uu____14896) in
                             uu____14889 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15038  ->
                     let uu____15039 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15039);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15061 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15063::uu____15064 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15069) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____15070 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____15101 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15115 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15115
                              | uu____15126 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2))))
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
              let uu____15138 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15138 in
            let uu____15139 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15139 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15152  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15163  ->
                      let uu____15164 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15165 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15164
                        uu____15165);
                 (let t1 =
                    let uu____15167 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15169 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15169) in
                    if uu____15167
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
                    | (UnivArgs (us',uu____15179))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15234 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15237 ->
                        let uu____15240 =
                          let uu____15241 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15241 in
                        failwith uu____15240
                  else norm cfg env stack t1))
and reduce_impure_comp:
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t in
              let stack1 = (Cfg cfg) :: stack in
              let cfg1 =
                let uu____15262 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15262
                then
                  let uu___131_15263 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___131_15263.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___131_15263.primitive_steps);
                    strong = (uu___131_15263.strong)
                  }
                else
                  (let uu___132_15265 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___132_15265.tcenv);
                     delta_level = (uu___132_15265.delta_level);
                     primitive_steps = (uu___132_15265.primitive_steps);
                     strong = (uu___132_15265.strong)
                   }) in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1
and do_reify_monadic:
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head2 = FStar_Syntax_Util.unascribe head1 in
                log cfg
                  (fun uu____15294  ->
                     let uu____15295 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15296 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15295
                       uu____15296);
                (let uu____15297 =
                   let uu____15298 = FStar_Syntax_Subst.compress head2 in
                   uu____15298.FStar_Syntax_Syntax.n in
                 match uu____15297 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15316 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15316 with
                      | (uu____15317,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15323 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15331 =
                                   let uu____15332 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15332.FStar_Syntax_Syntax.n in
                                 match uu____15331 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15338,uu____15339))
                                     ->
                                     let uu____15348 =
                                       let uu____15349 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15349.FStar_Syntax_Syntax.n in
                                     (match uu____15348 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15355,msrc,uu____15357))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15366 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15366
                                      | uu____15367 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15368 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15369 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15369 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___133_15374 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___133_15374.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___133_15374.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___133_15374.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15375 = FStar_List.tl stack in
                                    let uu____15376 =
                                      let uu____15377 =
                                        let uu____15380 =
                                          let uu____15381 =
                                            let uu____15394 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15394) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15381 in
                                        FStar_Syntax_Syntax.mk uu____15380 in
                                      uu____15377
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15375 uu____15376
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15410 =
                                      let uu____15411 = is_return body in
                                      match uu____15411 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15415;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15416;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15421 -> false in
                                    if uu____15410
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos in
                                       let head3 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         } in
                                       let body2 =
                                         let uu____15444 =
                                           let uu____15447 =
                                             let uu____15448 =
                                               let uu____15465 =
                                                 let uu____15468 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15468] in
                                               (uu____15465, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15448 in
                                           FStar_Syntax_Syntax.mk uu____15447 in
                                         uu____15444
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15484 =
                                           let uu____15485 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15485.FStar_Syntax_Syntax.n in
                                         match uu____15484 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15491::uu____15492::[])
                                             ->
                                             let uu____15499 =
                                               let uu____15502 =
                                                 let uu____15503 =
                                                   let uu____15510 =
                                                     let uu____15513 =
                                                       let uu____15514 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15514 in
                                                     let uu____15515 =
                                                       let uu____15518 =
                                                         let uu____15519 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15519 in
                                                       [uu____15518] in
                                                     uu____15513 ::
                                                       uu____15515 in
                                                   (bind1, uu____15510) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15503 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15502 in
                                             uu____15499
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15527 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15533 =
                                           let uu____15536 =
                                             let uu____15537 =
                                               let uu____15552 =
                                                 let uu____15555 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15556 =
                                                   let uu____15559 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15560 =
                                                     let uu____15563 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15564 =
                                                       let uu____15567 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15568 =
                                                         let uu____15571 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15572 =
                                                           let uu____15575 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15575] in
                                                         uu____15571 ::
                                                           uu____15572 in
                                                       uu____15567 ::
                                                         uu____15568 in
                                                     uu____15563 ::
                                                       uu____15564 in
                                                   uu____15559 :: uu____15560 in
                                                 uu____15555 :: uu____15556 in
                                               (bind_inst, uu____15552) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15537 in
                                           FStar_Syntax_Syntax.mk uu____15536 in
                                         uu____15533
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15586  ->
                                            let uu____15587 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15587);
                                       (let uu____15588 = FStar_List.tl stack in
                                        norm cfg env uu____15588 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15612 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15612 with
                      | (uu____15613,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15648 =
                                  let uu____15649 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15649.FStar_Syntax_Syntax.n in
                                match uu____15648 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15655) -> t2
                                | uu____15660 -> head3 in
                              let uu____15661 =
                                let uu____15662 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15662.FStar_Syntax_Syntax.n in
                              match uu____15661 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15668 -> FStar_Pervasives_Native.None in
                            let uu____15669 = maybe_extract_fv head3 in
                            match uu____15669 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15679 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15679
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15684 = maybe_extract_fv head4 in
                                  match uu____15684 with
                                  | FStar_Pervasives_Native.Some uu____15689
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15690 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15695 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15710 =
                              match uu____15710 with
                              | (e,q) ->
                                  let uu____15717 =
                                    let uu____15718 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15718.FStar_Syntax_Syntax.n in
                                  (match uu____15717 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15733 -> false) in
                            let uu____15734 =
                              let uu____15735 =
                                let uu____15742 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15742 :: args in
                              FStar_Util.for_some is_arg_impure uu____15735 in
                            if uu____15734
                            then
                              let uu____15747 =
                                let uu____15748 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15748 in
                              failwith uu____15747
                            else ());
                           (let uu____15750 = maybe_unfold_action head_app in
                            match uu____15750 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args)) in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body in
                                let uu____15787 = FStar_List.tl stack in
                                norm cfg env uu____15787 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15789) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15813 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15813 in
                     (log cfg
                        (fun uu____15817  ->
                           let uu____15818 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15818);
                      (let uu____15819 = FStar_List.tl stack in
                       norm cfg env uu____15819 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15821) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15946  ->
                               match uu____15946 with
                               | (pat,wopt,tm) ->
                                   let uu____15994 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15994))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____16026 = FStar_List.tl stack in
                     norm cfg env uu____16026 tm
                 | uu____16027 -> fallback ())
and reify_lift:
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv in
            log cfg
              (fun uu____16041  ->
                 let uu____16042 = FStar_Ident.string_of_lid msrc in
                 let uu____16043 = FStar_Ident.string_of_lid mtgt in
                 let uu____16044 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16042
                   uu____16043 uu____16044);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____16046 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____16046 with
               | (uu____16047,return_repr) ->
                   let return_inst =
                     let uu____16056 =
                       let uu____16057 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____16057.FStar_Syntax_Syntax.n in
                     match uu____16056 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16063::[]) ->
                         let uu____16070 =
                           let uu____16073 =
                             let uu____16074 =
                               let uu____16081 =
                                 let uu____16084 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____16084] in
                               (return_tm, uu____16081) in
                             FStar_Syntax_Syntax.Tm_uinst uu____16074 in
                           FStar_Syntax_Syntax.mk uu____16073 in
                         uu____16070 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16092 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____16095 =
                     let uu____16098 =
                       let uu____16099 =
                         let uu____16114 =
                           let uu____16117 = FStar_Syntax_Syntax.as_arg t in
                           let uu____16118 =
                             let uu____16121 = FStar_Syntax_Syntax.as_arg e in
                             [uu____16121] in
                           uu____16117 :: uu____16118 in
                         (return_inst, uu____16114) in
                       FStar_Syntax_Syntax.Tm_app uu____16099 in
                     FStar_Syntax_Syntax.mk uu____16098 in
                   uu____16095 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16130 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16130 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16133 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16133
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16134;
                     FStar_TypeChecker_Env.mtarget = uu____16135;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16136;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16151;
                     FStar_TypeChecker_Env.mtarget = uu____16152;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16153;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16177 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16178 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16177 t FStar_Syntax_Syntax.tun uu____16178)
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
                (fun uu____16234  ->
                   match uu____16234 with
                   | (a,imp) ->
                       let uu____16245 = norm cfg env [] a in
                       (uu____16245, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___134_16262 = comp1 in
            let uu____16265 =
              let uu____16266 =
                let uu____16275 = norm cfg env [] t in
                let uu____16276 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16275, uu____16276) in
              FStar_Syntax_Syntax.Total uu____16266 in
            {
              FStar_Syntax_Syntax.n = uu____16265;
              FStar_Syntax_Syntax.pos =
                (uu___134_16262.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___134_16262.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___135_16291 = comp1 in
            let uu____16294 =
              let uu____16295 =
                let uu____16304 = norm cfg env [] t in
                let uu____16305 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16304, uu____16305) in
              FStar_Syntax_Syntax.GTotal uu____16295 in
            {
              FStar_Syntax_Syntax.n = uu____16294;
              FStar_Syntax_Syntax.pos =
                (uu___135_16291.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_16291.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16357  ->
                      match uu____16357 with
                      | (a,i) ->
                          let uu____16368 = norm cfg env [] a in
                          (uu____16368, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___84_16379  ->
                      match uu___84_16379 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16383 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16383
                      | f -> f)) in
            let uu___136_16387 = comp1 in
            let uu____16390 =
              let uu____16391 =
                let uu___137_16392 = ct in
                let uu____16393 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16394 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16397 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16393;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___137_16392.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16394;
                  FStar_Syntax_Syntax.effect_args = uu____16397;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16391 in
            {
              FStar_Syntax_Syntax.n = uu____16390;
              FStar_Syntax_Syntax.pos =
                (uu___136_16387.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16387.FStar_Syntax_Syntax.vars)
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
            (let uu___138_16415 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___138_16415.tcenv);
               delta_level = (uu___138_16415.delta_level);
               primitive_steps = (uu___138_16415.primitive_steps);
               strong = (uu___138_16415.strong)
             }) env [] t in
        let non_info t =
          let uu____16420 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16420 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16423 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___139_16442 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___139_16442.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_16442.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16449 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16449
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
                    let uu___140_16460 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___140_16460.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___140_16460.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___140_16460.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags1
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___141_16462 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___141_16462.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___141_16462.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___141_16462.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___141_16462.FStar_Syntax_Syntax.flags)
                    } in
              let uu___142_16463 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___142_16463.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___142_16463.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16465 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16468  ->
        match uu____16468 with
        | (x,imp) ->
            let uu____16471 =
              let uu___143_16472 = x in
              let uu____16473 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___143_16472.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___143_16472.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16473
              } in
            (uu____16471, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16479 =
          FStar_List.fold_left
            (fun uu____16497  ->
               fun b  ->
                 match uu____16497 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16479 with | (nbs,uu____16537) -> FStar_List.rev nbs
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
            let uu____16553 =
              let uu___144_16554 = rc in
              let uu____16555 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___144_16554.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16555;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___144_16554.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16553
        | uu____16562 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16575  ->
               let uu____16576 = FStar_Syntax_Print.tag_of_term t in
               let uu____16577 = FStar_Syntax_Print.term_to_string t in
               let uu____16578 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16585 =
                 let uu____16586 =
                   let uu____16589 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16589 in
                 stack_to_string uu____16586 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16576 uu____16577 uu____16578 uu____16585);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16618 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16618
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16620 =
                     let uu____16621 =
                       let uu____16622 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16622 in
                     FStar_Util.string_of_int uu____16621 in
                   let uu____16627 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16628 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16620 uu____16627 uu____16628
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16682  ->
                     let uu____16683 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16683);
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
               let uu____16719 =
                 let uu___145_16720 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___145_16720.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___145_16720.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16719
           | (Arg (Univ uu____16721,uu____16722,uu____16723))::uu____16724 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16727,uu____16728))::uu____16729 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16745),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16798  ->
                     let uu____16799 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16799);
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
                  (let uu____16809 = FStar_ST.op_Bang m in
                   match uu____16809 with
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
                   | FStar_Pervasives_Native.Some (uu____16975,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____17022 =
                 log cfg
                   (fun uu____17026  ->
                      let uu____17027 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____17027);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____17031 =
                 let uu____17032 = FStar_Syntax_Subst.compress t in
                 uu____17032.FStar_Syntax_Syntax.n in
               (match uu____17031 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____17059 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____17059 in
                    (log cfg
                       (fun uu____17063  ->
                          let uu____17064 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____17064);
                     (let uu____17065 = FStar_List.tl stack in
                      norm cfg env1 uu____17065 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____17066);
                       FStar_Syntax_Syntax.pos = uu____17067;
                       FStar_Syntax_Syntax.vars = uu____17068;_},(e,uu____17070)::[])
                    -> norm cfg env1 stack' e
                | uu____17099 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17110 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17110
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17122  ->
                     let uu____17123 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17123);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17128 =
                   log cfg
                     (fun uu____17133  ->
                        let uu____17134 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17135 =
                          let uu____17136 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17153  ->
                                    match uu____17153 with
                                    | (p,uu____17163,uu____17164) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17136
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17134 uu____17135);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___85_17181  ->
                                match uu___85_17181 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17182 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___146_17186 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___146_17186.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___146_17186.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17218 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17239 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17299  ->
                                    fun uu____17300  ->
                                      match (uu____17299, uu____17300) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17391 = norm_pat env3 p1 in
                                          (match uu____17391 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17239 with
                           | (pats1,env3) ->
                               ((let uu___147_17473 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___147_17473.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___148_17492 = x in
                            let uu____17493 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17492.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17492.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17493
                            } in
                          ((let uu___149_17507 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___149_17507.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___150_17518 = x in
                            let uu____17519 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___150_17518.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___150_17518.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17519
                            } in
                          ((let uu___151_17533 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___151_17533.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___152_17549 = x in
                            let uu____17550 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_17549.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_17549.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17550
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___153_17557 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___153_17557.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17567 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17581 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17581 with
                                  | (p,wopt,e) ->
                                      let uu____17601 = norm_pat env1 p in
                                      (match uu____17601 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17626 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17626 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17632 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17632) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17642) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17647 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17648;
                         FStar_Syntax_Syntax.fv_delta = uu____17649;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17650;
                         FStar_Syntax_Syntax.fv_delta = uu____17651;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17652);_}
                       -> true
                   | uu____17659 -> false in
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
                   let uu____17804 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17804 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17891 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17930 ->
                                 let uu____17931 =
                                   let uu____17932 = is_cons head1 in
                                   Prims.op_Negation uu____17932 in
                                 FStar_Util.Inr uu____17931)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17957 =
                              let uu____17958 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17958.FStar_Syntax_Syntax.n in
                            (match uu____17957 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17976 ->
                                 let uu____17977 =
                                   let uu____17978 = is_cons head1 in
                                   Prims.op_Negation uu____17978 in
                                 FStar_Util.Inr uu____17977))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18047)::rest_a,(p1,uu____18050)::rest_p) ->
                       let uu____18094 = matches_pat t1 p1 in
                       (match uu____18094 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18143 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18249 = matches_pat scrutinee1 p1 in
                       (match uu____18249 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18289  ->
                                  let uu____18290 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18291 =
                                    let uu____18292 =
                                      FStar_List.map
                                        (fun uu____18302  ->
                                           match uu____18302 with
                                           | (uu____18307,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18292
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18290 uu____18291);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18338  ->
                                       match uu____18338 with
                                       | (bv,t1) ->
                                           let uu____18361 =
                                             let uu____18368 =
                                               let uu____18371 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18371 in
                                             let uu____18372 =
                                               let uu____18373 =
                                                 let uu____18404 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18404, false) in
                                               Clos uu____18373 in
                                             (uu____18368, uu____18372) in
                                           uu____18361 :: env2) env1 s in
                              let uu____18521 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18521))) in
                 let uu____18522 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18522
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___86_18543  ->
                match uu___86_18543 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18547 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18553 -> d in
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
            let uu___154_18578 = config s e in
            {
              steps = (uu___154_18578.steps);
              tcenv = (uu___154_18578.tcenv);
              delta_level = (uu___154_18578.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___154_18578.strong)
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
      fun t  -> let uu____18603 = config s e in norm_comp uu____18603 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18616 = config [] env in norm_universe uu____18616 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18629 = config [] env in ghost_to_pure_aux uu____18629 [] c
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
        let uu____18647 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18647 in
      let uu____18654 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18654
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___155_18656 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___155_18656.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___155_18656.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18659  ->
                    let uu____18660 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18660))
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
            ((let uu____18677 =
                let uu____18682 =
                  let uu____18683 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18683 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18682) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18677);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18694 = config [AllowUnboundUniverses] env in
          norm_comp uu____18694 [] c
        with
        | e ->
            ((let uu____18707 =
                let uu____18712 =
                  let uu____18713 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18713 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18712) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18707);
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
                   let uu____18750 =
                     let uu____18751 =
                       let uu____18758 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18758) in
                     FStar_Syntax_Syntax.Tm_refine uu____18751 in
                   mk uu____18750 t01.FStar_Syntax_Syntax.pos
               | uu____18763 -> t2)
          | uu____18764 -> t2 in
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
        let uu____18804 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18804 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18833 ->
                 let uu____18840 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18840 with
                  | (actuals,uu____18850,uu____18851) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18865 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18865 with
                         | (binders,args) ->
                             let uu____18882 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18882
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
      | uu____18890 ->
          let uu____18891 = FStar_Syntax_Util.head_and_args t in
          (match uu____18891 with
           | (head1,args) ->
               let uu____18928 =
                 let uu____18929 = FStar_Syntax_Subst.compress head1 in
                 uu____18929.FStar_Syntax_Syntax.n in
               (match uu____18928 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18932,thead) ->
                    let uu____18958 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18958 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19000 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___160_19008 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___160_19008.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___160_19008.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___160_19008.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___160_19008.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___160_19008.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___160_19008.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___160_19008.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___160_19008.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___160_19008.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___160_19008.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___160_19008.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___160_19008.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___160_19008.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___160_19008.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___160_19008.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___160_19008.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___160_19008.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___160_19008.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___160_19008.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___160_19008.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___160_19008.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___160_19008.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___160_19008.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___160_19008.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___160_19008.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___160_19008.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___160_19008.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___160_19008.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___160_19008.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___160_19008.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___160_19008.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____19000 with
                            | (uu____19009,ty,uu____19011) ->
                                eta_expand_with_type env t ty))
                | uu____19012 ->
                    let uu____19013 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___161_19021 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___161_19021.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___161_19021.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___161_19021.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___161_19021.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___161_19021.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___161_19021.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___161_19021.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___161_19021.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___161_19021.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___161_19021.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___161_19021.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___161_19021.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___161_19021.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___161_19021.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___161_19021.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___161_19021.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___161_19021.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___161_19021.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___161_19021.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___161_19021.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___161_19021.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___161_19021.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___161_19021.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___161_19021.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___161_19021.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___161_19021.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___161_19021.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___161_19021.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___161_19021.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___161_19021.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___161_19021.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____19013 with
                     | (uu____19022,ty,uu____19024) ->
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
            | (uu____19098,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19104,FStar_Util.Inl t) ->
                let uu____19110 =
                  let uu____19113 =
                    let uu____19114 =
                      let uu____19127 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19127) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19114 in
                  FStar_Syntax_Syntax.mk uu____19113 in
                uu____19110 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19131 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19131 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19158 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19213 ->
                    let uu____19214 =
                      let uu____19223 =
                        let uu____19224 = FStar_Syntax_Subst.compress t3 in
                        uu____19224.FStar_Syntax_Syntax.n in
                      (uu____19223, tc) in
                    (match uu____19214 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19249) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19286) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19325,FStar_Util.Inl uu____19326) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19349 -> failwith "Impossible") in
              (match uu____19158 with
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
          let uu____19454 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19454 with
          | (univ_names1,binders1,tc) ->
              let uu____19512 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19512)
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
          let uu____19547 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19547 with
          | (univ_names1,binders1,tc) ->
              let uu____19607 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19607)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19640 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19640 with
           | (univ_names1,binders1,typ1) ->
               let uu___162_19668 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___162_19668.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___162_19668.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___162_19668.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___162_19668.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___163_19689 = s in
          let uu____19690 =
            let uu____19691 =
              let uu____19700 = FStar_List.map (elim_uvars env) sigs in
              (uu____19700, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19691 in
          {
            FStar_Syntax_Syntax.sigel = uu____19690;
            FStar_Syntax_Syntax.sigrng =
              (uu___163_19689.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___163_19689.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___163_19689.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___163_19689.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19717 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19717 with
           | (univ_names1,uu____19735,typ1) ->
               let uu___164_19749 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19749.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19749.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19749.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19749.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19755 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19755 with
           | (univ_names1,uu____19773,typ1) ->
               let uu___165_19787 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___165_19787.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___165_19787.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___165_19787.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___165_19787.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19821 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19821 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19844 =
                            let uu____19845 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19845 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19844 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___166_19848 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___166_19848.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___166_19848.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___167_19849 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19849.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19849.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19849.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19849.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___168_19861 = s in
          let uu____19862 =
            let uu____19863 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19863 in
          {
            FStar_Syntax_Syntax.sigel = uu____19862;
            FStar_Syntax_Syntax.sigrng =
              (uu___168_19861.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___168_19861.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___168_19861.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___168_19861.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19867 = elim_uvars_aux_t env us [] t in
          (match uu____19867 with
           | (us1,uu____19885,t1) ->
               let uu___169_19899 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___169_19899.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___169_19899.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___169_19899.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___169_19899.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19900 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19902 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19902 with
           | (univs1,binders,signature) ->
               let uu____19930 =
                 let uu____19939 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19939 with
                 | (univs_opening,univs2) ->
                     let uu____19966 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19966) in
               (match uu____19930 with
                | (univs_opening,univs_closing) ->
                    let uu____19983 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19989 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19990 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19989, uu____19990) in
                    (match uu____19983 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20012 =
                           match uu____20012 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20030 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20030 with
                                | (us1,t1) ->
                                    let uu____20041 =
                                      let uu____20046 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20053 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20046, uu____20053) in
                                    (match uu____20041 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20066 =
                                           let uu____20071 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20080 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20071, uu____20080) in
                                         (match uu____20066 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20096 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20096 in
                                              let uu____20097 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20097 with
                                               | (uu____20118,uu____20119,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20134 =
                                                       let uu____20135 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20135 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20134 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20140 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20140 with
                           | (uu____20153,uu____20154,t1) -> t1 in
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
                             | uu____20214 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20231 =
                               let uu____20232 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20232.FStar_Syntax_Syntax.n in
                             match uu____20231 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20291 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20320 =
                               let uu____20321 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20321.FStar_Syntax_Syntax.n in
                             match uu____20320 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20342) ->
                                 let uu____20363 = destruct_action_body body in
                                 (match uu____20363 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20408 ->
                                 let uu____20409 = destruct_action_body t in
                                 (match uu____20409 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20458 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20458 with
                           | (action_univs,t) ->
                               let uu____20467 = destruct_action_typ_templ t in
                               (match uu____20467 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___170_20508 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___170_20508.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___170_20508.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___171_20510 = ed in
                           let uu____20511 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20512 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20513 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20514 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20515 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20516 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20517 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20518 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20519 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20520 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20521 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20522 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20523 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20524 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___171_20510.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___171_20510.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20511;
                             FStar_Syntax_Syntax.bind_wp = uu____20512;
                             FStar_Syntax_Syntax.if_then_else = uu____20513;
                             FStar_Syntax_Syntax.ite_wp = uu____20514;
                             FStar_Syntax_Syntax.stronger = uu____20515;
                             FStar_Syntax_Syntax.close_wp = uu____20516;
                             FStar_Syntax_Syntax.assert_p = uu____20517;
                             FStar_Syntax_Syntax.assume_p = uu____20518;
                             FStar_Syntax_Syntax.null_wp = uu____20519;
                             FStar_Syntax_Syntax.trivial = uu____20520;
                             FStar_Syntax_Syntax.repr = uu____20521;
                             FStar_Syntax_Syntax.return_repr = uu____20522;
                             FStar_Syntax_Syntax.bind_repr = uu____20523;
                             FStar_Syntax_Syntax.actions = uu____20524
                           } in
                         let uu___172_20527 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___172_20527.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___172_20527.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___172_20527.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___172_20527.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___87_20544 =
            match uu___87_20544 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20571 = elim_uvars_aux_t env us [] t in
                (match uu____20571 with
                 | (us1,uu____20595,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___173_20614 = sub_eff in
            let uu____20615 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20618 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___173_20614.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___173_20614.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20615;
              FStar_Syntax_Syntax.lift = uu____20618
            } in
          let uu___174_20621 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___174_20621.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___174_20621.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___174_20621.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___174_20621.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20631 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20631 with
           | (univ_names1,binders1,comp1) ->
               let uu___175_20665 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___175_20665.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___175_20665.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___175_20665.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___175_20665.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20676 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t