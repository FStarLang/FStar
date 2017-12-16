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
  fun uu___195_497  ->
    match uu___195_497 with
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
  | Cfg of cfg
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____772 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____808 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____844 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____901 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____943 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____999 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1039 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1071 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1107 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1123 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1148 .
    'Auu____1148 ->
      FStar_Range.range -> 'Auu____1148 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun r  ->
    fun t  ->
      let uu____1196 = FStar_ST.op_Bang r in
      match uu____1196 with
      | FStar_Pervasives_Native.Some uu____1265 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1339 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1339 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___196_1346  ->
    match uu___196_1346 with
    | Arg (c,uu____1348,uu____1349) ->
        let uu____1350 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1350
    | MemoLazy uu____1351 -> "MemoLazy"
    | Abs (uu____1358,bs,uu____1360,uu____1361,uu____1362) ->
        let uu____1367 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1367
    | UnivArgs uu____1372 -> "UnivArgs"
    | Match uu____1379 -> "Match"
    | App (uu____1386,t,uu____1388,uu____1389) ->
        let uu____1390 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1390
    | Meta (m,uu____1392) -> "Meta"
    | Let uu____1393 -> "Let"
    | Cfg uu____1402 -> "Cfg"
    | Debug (t,uu____1404) ->
        let uu____1405 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1405
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1413 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1413 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1429 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1429 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1442 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1442 then f () else ()
let is_empty: 'Auu____1446 . 'Auu____1446 Prims.list -> Prims.bool =
  fun uu___197_1452  ->
    match uu___197_1452 with | [] -> true | uu____1455 -> false
let lookup_bvar:
  'Auu____1462 'Auu____1463 .
    ('Auu____1463,'Auu____1462) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1462
  =
  fun env  ->
    fun x  ->
      try
        let uu____1487 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1487
      with
      | uu____1500 ->
          let uu____1501 =
            let uu____1502 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1502 in
          failwith uu____1501
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
          let uu____1539 =
            FStar_List.fold_left
              (fun uu____1565  ->
                 fun u1  ->
                   match uu____1565 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1590 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1590 with
                        | (k_u,n1) ->
                            let uu____1605 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1605
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1539 with
          | (uu____1623,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1648 =
                   let uu____1649 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1649 in
                 match uu____1648 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1667 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1676 ->
                   let uu____1677 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1677
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1683 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1692 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1701 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1708 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1708 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1725 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1725 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1733 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1741 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1741 with
                                  | (uu____1746,m) -> n1 <= m)) in
                        if uu____1733 then rest1 else us1
                    | uu____1751 -> us1)
               | uu____1756 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1760 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1760 in
        let uu____1763 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1763
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1765 = aux u in
           match uu____1765 with
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
          (fun uu____1869  ->
             let uu____1870 = FStar_Syntax_Print.tag_of_term t in
             let uu____1871 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1870
               uu____1871);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1878 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1880 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1905 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1906 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1907 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1908 ->
                  let uu____1925 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1925
                  then
                    let uu____1926 =
                      let uu____1927 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1928 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1927 uu____1928 in
                    failwith uu____1926
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1931 =
                    let uu____1932 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1932 in
                  mk uu____1931 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1939 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1939
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1941 = lookup_bvar env x in
                  (match uu____1941 with
                   | Univ uu____1944 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1948) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2060 = closures_as_binders_delayed cfg env bs in
                  (match uu____2060 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2088 =
                         let uu____2089 =
                           let uu____2106 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2106) in
                         FStar_Syntax_Syntax.Tm_abs uu____2089 in
                       mk uu____2088 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2137 = closures_as_binders_delayed cfg env bs in
                  (match uu____2137 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2179 =
                    let uu____2190 =
                      let uu____2197 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2197] in
                    closures_as_binders_delayed cfg env uu____2190 in
                  (match uu____2179 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2215 =
                         let uu____2216 =
                           let uu____2223 =
                             let uu____2224 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2224
                               FStar_Pervasives_Native.fst in
                           (uu____2223, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2216 in
                       mk uu____2215 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2315 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2315
                    | FStar_Util.Inr c ->
                        let uu____2329 = close_comp cfg env c in
                        FStar_Util.Inr uu____2329 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2345 =
                    let uu____2346 =
                      let uu____2373 = closure_as_term_delayed cfg env t11 in
                      (uu____2373, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2346 in
                  mk uu____2345 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2424 =
                    let uu____2425 =
                      let uu____2432 = closure_as_term_delayed cfg env t' in
                      let uu____2435 =
                        let uu____2436 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2436 in
                      (uu____2432, uu____2435) in
                    FStar_Syntax_Syntax.Tm_meta uu____2425 in
                  mk uu____2424 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2496 =
                    let uu____2497 =
                      let uu____2504 = closure_as_term_delayed cfg env t' in
                      let uu____2507 =
                        let uu____2508 =
                          let uu____2515 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2515) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2508 in
                      (uu____2504, uu____2507) in
                    FStar_Syntax_Syntax.Tm_meta uu____2497 in
                  mk uu____2496 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2534 =
                    let uu____2535 =
                      let uu____2542 = closure_as_term_delayed cfg env t' in
                      let uu____2545 =
                        let uu____2546 =
                          let uu____2555 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2555) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2546 in
                      (uu____2542, uu____2545) in
                    FStar_Syntax_Syntax.Tm_meta uu____2535 in
                  mk uu____2534 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2568 =
                    let uu____2569 =
                      let uu____2576 = closure_as_term_delayed cfg env t' in
                      (uu____2576, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2569 in
                  mk uu____2568 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2616  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2635 =
                    let uu____2646 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2646
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2665 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___216_2677 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___216_2677.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___216_2677.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2665)) in
                  (match uu____2635 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___217_2693 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___217_2693.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___217_2693.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2704,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2763  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2788 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2788
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2808  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2830 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2830
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___218_2842 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___218_2842.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___218_2842.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___219_2843 = lb in
                    let uu____2844 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___219_2843.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___219_2843.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2844
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2874  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2963 =
                    match uu____2963 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3018 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3039 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3099  ->
                                        fun uu____3100  ->
                                          match (uu____3099, uu____3100) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3191 =
                                                norm_pat env3 p1 in
                                              (match uu____3191 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3039 with
                               | (pats1,env3) ->
                                   ((let uu___220_3273 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___220_3273.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___221_3292 = x in
                                let uu____3293 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___221_3292.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___221_3292.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3293
                                } in
                              ((let uu___222_3307 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___222_3307.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___223_3318 = x in
                                let uu____3319 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___223_3318.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___223_3318.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3319
                                } in
                              ((let uu___224_3333 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___224_3333.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___225_3349 = x in
                                let uu____3350 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___225_3349.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___225_3349.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3350
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___226_3357 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___226_3357.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3360 = norm_pat env1 pat in
                        (match uu____3360 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3389 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3389 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3395 =
                    let uu____3396 =
                      let uu____3419 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3419) in
                    FStar_Syntax_Syntax.Tm_match uu____3396 in
                  mk uu____3395 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3505 -> closure_as_term cfg env t
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
        | uu____3531 ->
            FStar_List.map
              (fun uu____3548  ->
                 match uu____3548 with
                 | (x,imp) ->
                     let uu____3567 = closure_as_term_delayed cfg env x in
                     (uu____3567, imp)) args
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
        let uu____3581 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3630  ->
                  fun uu____3631  ->
                    match (uu____3630, uu____3631) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___227_3701 = b in
                          let uu____3702 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___227_3701.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___227_3701.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3702
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3581 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3795 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3808 = closure_as_term_delayed cfg env t in
                 let uu____3809 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3808 uu____3809
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3822 = closure_as_term_delayed cfg env t in
                 let uu____3823 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3822 uu____3823
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
                        (fun uu___198_3849  ->
                           match uu___198_3849 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3853 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3853
                           | f -> f)) in
                 let uu____3857 =
                   let uu___228_3858 = c1 in
                   let uu____3859 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3859;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___228_3858.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3857)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___199_3869  ->
            match uu___199_3869 with
            | FStar_Syntax_Syntax.DECREASES uu____3870 -> false
            | uu____3873 -> true))
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
                   (fun uu___200_3891  ->
                      match uu___200_3891 with
                      | FStar_Syntax_Syntax.DECREASES uu____3892 -> false
                      | uu____3895 -> true)) in
            let rc1 =
              let uu___229_3897 = rc in
              let uu____3898 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___229_3897.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3898;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3905 -> lopt
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
    let uu____3995 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3995 in
  let arg_as_bounded_int uu____4023 =
    match uu____4023 with
    | (a,uu____4035) ->
        let uu____4042 =
          let uu____4043 = FStar_Syntax_Subst.compress a in
          uu____4043.FStar_Syntax_Syntax.n in
        (match uu____4042 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4053;
                FStar_Syntax_Syntax.vars = uu____4054;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4056;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4057;_},uu____4058)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4097 =
               let uu____4102 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4102) in
             FStar_Pervasives_Native.Some uu____4097
         | uu____4107 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4149 = f a in FStar_Pervasives_Native.Some uu____4149
    | uu____4150 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4200 = f a0 a1 in FStar_Pervasives_Native.Some uu____4200
    | uu____4201 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4250 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4250 in
  let binary_op as_a f res args =
    let uu____4306 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4306 in
  let as_primitive_step uu____4330 =
    match uu____4330 with
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
           let uu____4378 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4378) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4406 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4406) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4427 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4427) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4455 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4455) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4483 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4483) in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4600 =
          let uu____4609 = as_a a in
          let uu____4612 = as_b b in (uu____4609, uu____4612) in
        (match uu____4600 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4627 =
               let uu____4628 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4628 in
             FStar_Pervasives_Native.Some uu____4627
         | uu____4629 -> FStar_Pervasives_Native.None)
    | uu____4638 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4652 =
        let uu____4653 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4653 in
      mk uu____4652 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4663 =
      let uu____4666 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4666 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4663 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4698 =
      let uu____4699 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4699 in
    FStar_Syntax_Embeddings.embed_int rng uu____4698 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4717 = arg_as_string a1 in
        (match uu____4717 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4723 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4723 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4736 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4736
              | uu____4737 -> FStar_Pervasives_Native.None)
         | uu____4742 -> FStar_Pervasives_Native.None)
    | uu____4745 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4755 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4755 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4779 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4790 =
          let uu____4811 = arg_as_string fn in
          let uu____4814 = arg_as_int from_line in
          let uu____4817 = arg_as_int from_col in
          let uu____4820 = arg_as_int to_line in
          let uu____4823 = arg_as_int to_col in
          (uu____4811, uu____4814, uu____4817, uu____4820, uu____4823) in
        (match uu____4790 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4854 =
                 let uu____4855 = FStar_BigInt.to_int_fs from_l in
                 let uu____4856 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4855 uu____4856 in
               let uu____4857 =
                 let uu____4858 = FStar_BigInt.to_int_fs to_l in
                 let uu____4859 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4858 uu____4859 in
               FStar_Range.mk_range fn1 uu____4854 uu____4857 in
             let uu____4860 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4860
         | uu____4865 -> FStar_Pervasives_Native.None)
    | uu____4886 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4913)::(a1,uu____4915)::(a2,uu____4917)::[] ->
        let uu____4954 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4954 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4967 -> FStar_Pervasives_Native.None)
    | uu____4968 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4995)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5004 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5028 =
      let uu____5043 =
        let uu____5058 =
          let uu____5073 =
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
                                              let uu____5341 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5341,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5348 =
                                              let uu____5363 =
                                                let uu____5376 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5376,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5387 =
                                                let uu____5402 =
                                                  let uu____5417 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5417,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5426 =
                                                  let uu____5443 =
                                                    let uu____5458 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"] in
                                                    (uu____5458,
                                                      (Prims.parse_int "5"),
                                                      mk_range1) in
                                                  let uu____5467 =
                                                    let uu____5484 =
                                                      let uu____5503 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"] in
                                                      (uu____5503,
                                                        (Prims.parse_int "1"),
                                                        idstep) in
                                                    [uu____5484] in
                                                  uu____5443 :: uu____5467 in
                                                uu____5402 :: uu____5426 in
                                              uu____5363 :: uu____5387 in
                                            uu____5328 :: uu____5348 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5313 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5298 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5283 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5268 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5253 in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5721 =
                                              FStar_BigInt.to_int_fs x in
                                            FStar_String.make uu____5721 y)))
                                  :: uu____5238 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5223 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5208 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5193 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5178 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5163 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5867 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5867)))
                      :: uu____5148 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5893 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5893)))
                    :: uu____5133 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5919 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5919)))
                  :: uu____5118 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5945 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5945)))
                :: uu____5103 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5088 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5073 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5058 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5043 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5028 in
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
      let uu____6095 =
        let uu____6096 =
          let uu____6097 = FStar_Syntax_Syntax.as_arg c in [uu____6097] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6096 in
      uu____6095 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6132 =
              let uu____6145 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6145, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6165  ->
                        fun uu____6166  ->
                          match (uu____6165, uu____6166) with
                          | ((int_to_t1,x),(uu____6185,y)) ->
                              let uu____6195 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____6195))) in
            let uu____6196 =
              let uu____6211 =
                let uu____6224 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6224, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6244  ->
                          fun uu____6245  ->
                            match (uu____6244, uu____6245) with
                            | ((int_to_t1,x),(uu____6264,y)) ->
                                let uu____6274 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6274))) in
              let uu____6275 =
                let uu____6290 =
                  let uu____6303 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6303, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6323  ->
                            fun uu____6324  ->
                              match (uu____6323, uu____6324) with
                              | ((int_to_t1,x),(uu____6343,y)) ->
                                  let uu____6353 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6353))) in
                [uu____6290] in
              uu____6211 :: uu____6275 in
            uu____6132 :: uu____6196)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6443)::(a1,uu____6445)::(a2,uu____6447)::[] ->
        let uu____6484 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6484 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___230_6490 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___230_6490.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___230_6490.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___231_6494 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___231_6494.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___231_6494.FStar_Syntax_Syntax.vars)
                })
         | uu____6495 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6497)::uu____6498::(a1,uu____6500)::(a2,uu____6502)::[] ->
        let uu____6551 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6551 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___230_6557 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___230_6557.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___230_6557.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___231_6561 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___231_6561.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___231_6561.FStar_Syntax_Syntax.vars)
                })
         | uu____6562 -> FStar_Pervasives_Native.None)
    | uu____6563 -> failwith "Unexpected number of arguments" in
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
      let uu____6582 =
        let uu____6583 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6583 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6582
    with | uu____6589 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6593 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6593) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6653  ->
           fun subst1  ->
             match uu____6653 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6695)) ->
                      let uu____6754 = b in
                      (match uu____6754 with
                       | (bv,uu____6762) ->
                           let uu____6763 =
                             let uu____6764 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6764 in
                           if uu____6763
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6769 = unembed_binder term1 in
                              match uu____6769 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6776 =
                                      let uu___234_6777 = bv in
                                      let uu____6778 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___234_6777.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___234_6777.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6778
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6776 in
                                  let b_for_x =
                                    let uu____6782 =
                                      let uu____6789 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6789) in
                                    FStar_Syntax_Syntax.NT uu____6782 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___201_6798  ->
                                         match uu___201_6798 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6799,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6801;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6802;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6807 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6808 -> subst1)) env []
let reduce_primops:
  'Auu____6825 'Auu____6826 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6826) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6825 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6867 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6867
          then tm
          else
            (let uu____6869 = FStar_Syntax_Util.head_and_args tm in
             match uu____6869 with
             | (head1,args) ->
                 let uu____6906 =
                   let uu____6907 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6907.FStar_Syntax_Syntax.n in
                 (match uu____6906 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6911 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6911 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6928  ->
                                   let uu____6929 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6930 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6937 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6929 uu____6930 uu____6937);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6942  ->
                                   let uu____6943 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6943);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6946  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6948 =
                                 prim_step.interpretation psc args in
                               match uu____6948 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6954  ->
                                         let uu____6955 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6955);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6961  ->
                                         let uu____6962 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6963 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6962 uu____6963);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6964 ->
                           (log_primops cfg
                              (fun uu____6968  ->
                                 let uu____6969 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6969);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6973  ->
                            let uu____6974 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6974);
                       (match args with
                        | (a1,uu____6976)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6993 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7005  ->
                            let uu____7006 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7006);
                       (match args with
                        | (t,uu____7008)::(r,uu____7010)::[] ->
                            let uu____7037 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7037 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___235_7041 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___235_7041.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___235_7041.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7044 -> tm))
                  | uu____7053 -> tm))
let reduce_equality:
  'Auu____7058 'Auu____7059 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7059) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7058 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___236_7097 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___236_7097.tcenv);
           delta_level = (uu___236_7097.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___236_7097.strong)
         }) tm
let maybe_simplify_aux:
  'Auu____7104 'Auu____7105 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7105) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7104 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7147 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7147
          then tm1
          else
            (let w t =
               let uu___237_7159 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___237_7159.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___237_7159.FStar_Syntax_Syntax.vars)
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
               | uu____7176 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7181 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7181
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7202 =
                 match uu____7202 with
                 | (t1,q) ->
                     let uu____7215 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7215 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7243 -> (t1, q)) in
               let uu____7252 = FStar_Syntax_Util.head_and_args t in
               match uu____7252 with
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
                         FStar_Syntax_Syntax.pos = uu____7349;
                         FStar_Syntax_Syntax.vars = uu____7350;_},uu____7351);
                    FStar_Syntax_Syntax.pos = uu____7352;
                    FStar_Syntax_Syntax.vars = uu____7353;_},args)
                 ->
                 let uu____7379 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7379
                 then
                   let uu____7380 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7380 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7435)::
                        (uu____7436,(arg,uu____7438))::[] ->
                        maybe_auto_squash arg
                    | (uu____7503,(arg,uu____7505))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7506)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7571)::uu____7572::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7635::(FStar_Pervasives_Native.Some (false
                                   ),uu____7636)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7699 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7715 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7715
                    then
                      let uu____7716 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7716 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7771)::uu____7772::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7835::(FStar_Pervasives_Native.Some (true
                                     ),uu____7836)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7899)::
                          (uu____7900,(arg,uu____7902))::[] ->
                          maybe_auto_squash arg
                      | (uu____7967,(arg,uu____7969))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7970)::[]
                          -> maybe_auto_squash arg
                      | uu____8035 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8051 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8051
                       then
                         let uu____8052 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8052 with
                         | uu____8107::(FStar_Pervasives_Native.Some (true
                                        ),uu____8108)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8171)::uu____8172::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8235)::
                             (uu____8236,(arg,uu____8238))::[] ->
                             maybe_auto_squash arg
                         | (uu____8303,(p,uu____8305))::(uu____8306,(q,uu____8308))::[]
                             ->
                             let uu____8373 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8373
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8375 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8391 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8391
                          then
                            let uu____8392 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8392 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8447)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8486)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8525 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8541 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8541
                             then
                               match args with
                               | (t,uu____8543)::[] ->
                                   let uu____8560 =
                                     let uu____8561 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8561.FStar_Syntax_Syntax.n in
                                   (match uu____8560 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8564::[],body,uu____8566) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8593 -> tm1)
                                    | uu____8596 -> tm1)
                               | (uu____8597,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8598))::
                                   (t,uu____8600)::[] ->
                                   let uu____8639 =
                                     let uu____8640 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8640.FStar_Syntax_Syntax.n in
                                   (match uu____8639 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8643::[],body,uu____8645) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8672 -> tm1)
                                    | uu____8675 -> tm1)
                               | uu____8676 -> tm1
                             else
                               (let uu____8686 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8686
                                then
                                  match args with
                                  | (t,uu____8688)::[] ->
                                      let uu____8705 =
                                        let uu____8706 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8706.FStar_Syntax_Syntax.n in
                                      (match uu____8705 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8709::[],body,uu____8711)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8738 -> tm1)
                                       | uu____8741 -> tm1)
                                  | (uu____8742,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8743))::(t,uu____8745)::[] ->
                                      let uu____8784 =
                                        let uu____8785 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8785.FStar_Syntax_Syntax.n in
                                      (match uu____8784 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8788::[],body,uu____8790)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8817 -> tm1)
                                       | uu____8820 -> tm1)
                                  | uu____8821 -> tm1
                                else
                                  (let uu____8831 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8831
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8832;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8833;_},uu____8834)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8851;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8852;_},uu____8853)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8870 -> tm1
                                   else
                                     (let uu____8880 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8880 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8900 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8910;
                    FStar_Syntax_Syntax.vars = uu____8911;_},args)
                 ->
                 let uu____8933 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8933
                 then
                   let uu____8934 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8934 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8989)::
                        (uu____8990,(arg,uu____8992))::[] ->
                        maybe_auto_squash arg
                    | (uu____9057,(arg,uu____9059))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9060)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9125)::uu____9126::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9189::(FStar_Pervasives_Native.Some (false
                                   ),uu____9190)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9253 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9269 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9269
                    then
                      let uu____9270 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9270 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9325)::uu____9326::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9389::(FStar_Pervasives_Native.Some (true
                                     ),uu____9390)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9453)::
                          (uu____9454,(arg,uu____9456))::[] ->
                          maybe_auto_squash arg
                      | (uu____9521,(arg,uu____9523))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9524)::[]
                          -> maybe_auto_squash arg
                      | uu____9589 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9605 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9605
                       then
                         let uu____9606 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9606 with
                         | uu____9661::(FStar_Pervasives_Native.Some (true
                                        ),uu____9662)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9725)::uu____9726::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9789)::
                             (uu____9790,(arg,uu____9792))::[] ->
                             maybe_auto_squash arg
                         | (uu____9857,(p,uu____9859))::(uu____9860,(q,uu____9862))::[]
                             ->
                             let uu____9927 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9927
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9929 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9945 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9945
                          then
                            let uu____9946 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9946 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10001)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10040)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10079 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10095 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10095
                             then
                               match args with
                               | (t,uu____10097)::[] ->
                                   let uu____10114 =
                                     let uu____10115 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10115.FStar_Syntax_Syntax.n in
                                   (match uu____10114 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10118::[],body,uu____10120) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10147 -> tm1)
                                    | uu____10150 -> tm1)
                               | (uu____10151,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10152))::
                                   (t,uu____10154)::[] ->
                                   let uu____10193 =
                                     let uu____10194 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10194.FStar_Syntax_Syntax.n in
                                   (match uu____10193 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10197::[],body,uu____10199) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10226 -> tm1)
                                    | uu____10229 -> tm1)
                               | uu____10230 -> tm1
                             else
                               (let uu____10240 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10240
                                then
                                  match args with
                                  | (t,uu____10242)::[] ->
                                      let uu____10259 =
                                        let uu____10260 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10260.FStar_Syntax_Syntax.n in
                                      (match uu____10259 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10263::[],body,uu____10265)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10292 -> tm1)
                                       | uu____10295 -> tm1)
                                  | (uu____10296,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10297))::(t,uu____10299)::[] ->
                                      let uu____10338 =
                                        let uu____10339 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10339.FStar_Syntax_Syntax.n in
                                      (match uu____10338 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10342::[],body,uu____10344)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10371 -> tm1)
                                       | uu____10374 -> tm1)
                                  | uu____10375 -> tm1
                                else
                                  (let uu____10385 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10385
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10386;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10387;_},uu____10388)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10405;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10406;_},uu____10407)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10424 -> tm1
                                   else
                                     (let uu____10434 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10434 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10454 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10463 -> tm1)
let maybe_simplify:
  'Auu____10470 'Auu____10471 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10471) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10470 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10514 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10514
           then
             let uu____10515 = FStar_Syntax_Print.term_to_string tm in
             let uu____10516 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10515 uu____10516
           else ());
          tm'
let is_norm_request:
  'Auu____10522 .
    FStar_Syntax_Syntax.term -> 'Auu____10522 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10535 =
        let uu____10542 =
          let uu____10543 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10543.FStar_Syntax_Syntax.n in
        (uu____10542, args) in
      match uu____10535 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10549::uu____10550::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10554::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10559::uu____10560::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10563 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___202_10574  ->
    match uu___202_10574 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10580 =
          let uu____10583 =
            let uu____10584 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10584 in
          [uu____10583] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10580
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10599 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10599) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10637 =
          let uu____10640 =
            let uu____10645 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10645 s in
          FStar_All.pipe_right uu____10640 FStar_Util.must in
        FStar_All.pipe_right uu____10637 tr_norm_steps in
      match args with
      | uu____10670::(tm,uu____10672)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10695)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10710)::uu____10711::(tm,uu____10713)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10753 =
              let uu____10756 = full_norm steps in parse_steps uu____10756 in
            Beta :: uu____10753 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10765 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___203_10782  ->
    match uu___203_10782 with
    | (App
        (uu____10785,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10786;
                       FStar_Syntax_Syntax.vars = uu____10787;_},uu____10788,uu____10789))::uu____10790
        -> true
    | uu____10797 -> false
let firstn:
  'Auu____10803 .
    Prims.int ->
      'Auu____10803 Prims.list ->
        ('Auu____10803 Prims.list,'Auu____10803 Prims.list)
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
          (uu____10839,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10840;
                         FStar_Syntax_Syntax.vars = uu____10841;_},uu____10842,uu____10843))::uu____10844
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10851 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11006  ->
               let uu____11007 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11008 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11009 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11016 =
                 let uu____11017 =
                   let uu____11020 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11020 in
                 stack_to_string uu____11017 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11007 uu____11008 uu____11009 uu____11016);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11043 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11068 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11085 =
                 let uu____11086 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11087 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11086 uu____11087 in
               failwith uu____11085
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11088 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11105 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11106 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11107;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11108;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11111;
                 FStar_Syntax_Syntax.fv_delta = uu____11112;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11113;
                 FStar_Syntax_Syntax.fv_delta = uu____11114;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11115);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11123 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11123 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11129  ->
                     let uu____11130 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11131 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11130 uu____11131);
                if b
                then
                  (let uu____11132 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11132 t1 fv)
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
                 let uu___238_11171 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___238_11171.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___238_11171.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11204 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11204) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___239_11212 = cfg in
                 let uu____11213 =
                   FStar_List.filter
                     (fun uu___204_11216  ->
                        match uu___204_11216 with
                        | UnfoldOnly uu____11217 -> false
                        | NoDeltaSteps  -> false
                        | uu____11220 -> true) cfg.steps in
                 {
                   steps = uu____11213;
                   tcenv = (uu___239_11212.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___239_11212.primitive_steps);
                   strong = (uu___239_11212.strong)
                 } in
               let uu____11221 = get_norm_request (norm cfg' env []) args in
               (match uu____11221 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11237 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___205_11242  ->
                                match uu___205_11242 with
                                | UnfoldUntil uu____11243 -> true
                                | UnfoldOnly uu____11244 -> true
                                | uu____11247 -> false)) in
                      if uu____11237
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___240_11252 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___240_11252.tcenv);
                        delta_level;
                        primitive_steps = (uu___240_11252.primitive_steps);
                        strong = (uu___240_11252.strong)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11259 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11259
                      then
                        let uu____11262 =
                          let uu____11263 =
                            let uu____11268 = FStar_Util.now () in
                            (t1, uu____11268) in
                          Debug uu____11263 in
                        uu____11262 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11272 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11272
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11279 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11279
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11282 =
                      let uu____11289 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11289, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11282 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___206_11302  ->
                         match uu___206_11302 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11305 =
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
                 if uu____11305
                 then false
                 else
                   (let uu____11307 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___207_11314  ->
                              match uu___207_11314 with
                              | UnfoldOnly uu____11315 -> true
                              | uu____11318 -> false)) in
                    match uu____11307 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11322 -> should_delta) in
               (log cfg
                  (fun uu____11330  ->
                     let uu____11331 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11332 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11333 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11331 uu____11332 uu____11333);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11336 = lookup_bvar env x in
               (match uu____11336 with
                | Univ uu____11339 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11388 = FStar_ST.op_Bang r in
                      (match uu____11388 with
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
                                 norm cfg env2 stack t'
                             | uu____11551 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
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
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11777  ->
                          let uu____11778 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11778);
                     norm cfg env stack1 t1)
                | (Debug uu____11779)::uu____11780 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11787 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11787
                    else
                      (let uu____11789 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11789 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11831  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11859 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11859
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11869 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11869)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___241_11874 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___241_11874.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___241_11874.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11875 -> lopt in
                           (log cfg
                              (fun uu____11881  ->
                                 let uu____11882 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11882);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___242_11891 = cfg in
                               {
                                 steps = (uu___242_11891.steps);
                                 tcenv = (uu___242_11891.tcenv);
                                 delta_level = (uu___242_11891.delta_level);
                                 primitive_steps =
                                   (uu___242_11891.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11902)::uu____11903 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11910 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11910
                    else
                      (let uu____11912 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11912 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11954  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11982 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11982
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11992 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11992)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___241_11997 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___241_11997.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___241_11997.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11998 -> lopt in
                           (log cfg
                              (fun uu____12004  ->
                                 let uu____12005 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12005);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___242_12014 = cfg in
                               {
                                 steps = (uu___242_12014.steps);
                                 tcenv = (uu___242_12014.tcenv);
                                 delta_level = (uu___242_12014.delta_level);
                                 primitive_steps =
                                   (uu___242_12014.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12025)::uu____12026 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12037 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12037
                    else
                      (let uu____12039 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12039 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12081  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12109 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12109
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12119 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12119)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___241_12124 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___241_12124.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___241_12124.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12125 -> lopt in
                           (log cfg
                              (fun uu____12131  ->
                                 let uu____12132 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12132);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___242_12141 = cfg in
                               {
                                 steps = (uu___242_12141.steps);
                                 tcenv = (uu___242_12141.tcenv);
                                 delta_level = (uu___242_12141.delta_level);
                                 primitive_steps =
                                   (uu___242_12141.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12152)::uu____12153 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12164 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12164
                    else
                      (let uu____12166 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12166 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12208  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12236 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12236
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12246 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12246)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___241_12251 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___241_12251.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___241_12251.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12252 -> lopt in
                           (log cfg
                              (fun uu____12258  ->
                                 let uu____12259 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12259);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___242_12268 = cfg in
                               {
                                 steps = (uu___242_12268.steps);
                                 tcenv = (uu___242_12268.tcenv);
                                 delta_level = (uu___242_12268.delta_level);
                                 primitive_steps =
                                   (uu___242_12268.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12279)::uu____12280 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12295 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12295
                    else
                      (let uu____12297 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12297 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12339  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12367 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12367
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12377 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12377)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___241_12382 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___241_12382.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___241_12382.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12383 -> lopt in
                           (log cfg
                              (fun uu____12389  ->
                                 let uu____12390 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12390);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___242_12399 = cfg in
                               {
                                 steps = (uu___242_12399.steps);
                                 tcenv = (uu___242_12399.tcenv);
                                 delta_level = (uu___242_12399.delta_level);
                                 primitive_steps =
                                   (uu___242_12399.primitive_steps);
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
                      let uu____12410 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12410
                    else
                      (let uu____12412 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12412 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12454  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12482 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12482
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12492 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12492)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___241_12497 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___241_12497.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___241_12497.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12498 -> lopt in
                           (log cfg
                              (fun uu____12504  ->
                                 let uu____12505 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12505);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___242_12514 = cfg in
                               {
                                 steps = (uu___242_12514.steps);
                                 tcenv = (uu___242_12514.tcenv);
                                 delta_level = (uu___242_12514.delta_level);
                                 primitive_steps =
                                   (uu___242_12514.primitive_steps);
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
                      (fun uu____12563  ->
                         fun stack1  ->
                           match uu____12563 with
                           | (a,aq) ->
                               let uu____12575 =
                                 let uu____12576 =
                                   let uu____12583 =
                                     let uu____12584 =
                                       let uu____12615 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12615, false) in
                                     Clos uu____12584 in
                                   (uu____12583, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12576 in
                               uu____12575 :: stack1) args) in
               (log cfg
                  (fun uu____12691  ->
                     let uu____12692 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12692);
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
                             ((let uu___243_12728 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___243_12728.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___243_12728.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12729 ->
                      let uu____12734 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12734)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12737 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12737 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12768 =
                          let uu____12769 =
                            let uu____12776 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___244_12778 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___244_12778.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___244_12778.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12776) in
                          FStar_Syntax_Syntax.Tm_refine uu____12769 in
                        mk uu____12768 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12797 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12797
               else
                 (let uu____12799 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12799 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12807 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12831  -> dummy :: env1) env) in
                        norm_comp cfg uu____12807 c1 in
                      let t2 =
                        let uu____12853 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12853 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12912)::uu____12913 ->
                    (log cfg
                       (fun uu____12924  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12925)::uu____12926 ->
                    (log cfg
                       (fun uu____12937  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12938,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12939;
                                   FStar_Syntax_Syntax.vars = uu____12940;_},uu____12941,uu____12942))::uu____12943
                    ->
                    (log cfg
                       (fun uu____12952  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12953)::uu____12954 ->
                    (log cfg
                       (fun uu____12965  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12966 ->
                    (log cfg
                       (fun uu____12969  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12973  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12990 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____12990
                         | FStar_Util.Inr c ->
                             let uu____12998 = norm_comp cfg env c in
                             FStar_Util.Inr uu____12998 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13011 =
                               let uu____13012 =
                                 let uu____13039 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13039, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13012 in
                             mk uu____13011 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13058 ->
                           let uu____13059 =
                             let uu____13060 =
                               let uu____13061 =
                                 let uu____13088 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13088, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13061 in
                             mk uu____13060 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13059))))
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
                         let uu____13198 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13198 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___245_13218 = cfg in
                               let uu____13219 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___245_13218.steps);
                                 tcenv = uu____13219;
                                 delta_level = (uu___245_13218.delta_level);
                                 primitive_steps =
                                   (uu___245_13218.primitive_steps);
                                 strong = (uu___245_13218.strong)
                               } in
                             let norm1 t2 =
                               let uu____13224 =
                                 let uu____13225 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13225 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13224 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___246_13228 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___246_13228.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___246_13228.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13229 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13229
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13240,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13241;
                               FStar_Syntax_Syntax.lbunivs = uu____13242;
                               FStar_Syntax_Syntax.lbtyp = uu____13243;
                               FStar_Syntax_Syntax.lbeff = uu____13244;
                               FStar_Syntax_Syntax.lbdef = uu____13245;_}::uu____13246),uu____13247)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13283 =
                 (let uu____13286 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13286) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13288 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13288))) in
               if uu____13283
               then
                 let binder =
                   let uu____13290 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13290 in
                 let env1 =
                   let uu____13300 =
                     let uu____13307 =
                       let uu____13308 =
                         let uu____13339 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13339,
                           false) in
                       Clos uu____13308 in
                     ((FStar_Pervasives_Native.Some binder), uu____13307) in
                   uu____13300 :: env in
                 (log cfg
                    (fun uu____13424  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13426 =
                    let uu____13431 =
                      let uu____13432 =
                        let uu____13433 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13433
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13432] in
                    FStar_Syntax_Subst.open_term uu____13431 body in
                  match uu____13426 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13442  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13450 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13450 in
                          FStar_Util.Inl
                            (let uu___247_13460 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___247_13460.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___247_13460.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13463  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___248_13465 = lb in
                           let uu____13466 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___248_13465.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___248_13465.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13466
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13501  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___249_13524 = cfg in
                           {
                             steps = (uu___249_13524.steps);
                             tcenv = (uu___249_13524.tcenv);
                             delta_level = (uu___249_13524.delta_level);
                             primitive_steps =
                               (uu___249_13524.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13527  ->
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
               let uu____13544 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13544 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13580 =
                               let uu___250_13581 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___250_13581.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___250_13581.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13580 in
                           let uu____13582 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13582 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13608 =
                                   FStar_List.map (fun uu____13624  -> dummy)
                                     lbs1 in
                                 let uu____13625 =
                                   let uu____13634 =
                                     FStar_List.map
                                       (fun uu____13654  -> dummy) xs1 in
                                   FStar_List.append uu____13634 env in
                                 FStar_List.append uu____13608 uu____13625 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13678 =
                                       let uu___251_13679 = rc in
                                       let uu____13680 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___251_13679.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13680;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___251_13679.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13678
                                 | uu____13687 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___252_13691 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___252_13691.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___252_13691.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13701 =
                        FStar_List.map (fun uu____13717  -> dummy) lbs2 in
                      FStar_List.append uu____13701 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13725 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13725 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___253_13741 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___253_13741.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___253_13741.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13768 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13768
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13787 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13863  ->
                        match uu____13863 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___254_13984 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___254_13984.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___254_13984.FStar_Syntax_Syntax.sort)
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
               (match uu____13787 with
                | (rec_env,memos,uu____14181) ->
                    let uu____14234 =
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
                             let uu____14771 =
                               let uu____14778 =
                                 let uu____14779 =
                                   let uu____14810 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14810, false) in
                                 Clos uu____14779 in
                               (FStar_Pervasives_Native.None, uu____14778) in
                             uu____14771 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14912  ->
                     let uu____14913 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14913);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14935 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14937::uu____14938 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14943) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14944 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14975 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14989 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14989
                              | uu____15000 -> m in
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
              let uu____15012 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15012 in
            let uu____15013 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15013 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15026  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15037  ->
                      let uu____15038 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15039 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15038
                        uu____15039);
                 (let t1 =
                    let uu____15041 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15043 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15043) in
                    if uu____15041
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
                    | (UnivArgs (us',uu____15053))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15108 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15111 ->
                        let uu____15114 =
                          let uu____15115 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15115 in
                        failwith uu____15114
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
                let uu____15136 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15136
                then
                  let uu___255_15137 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___255_15137.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___255_15137.primitive_steps);
                    strong = (uu___255_15137.strong)
                  }
                else
                  (let uu___256_15139 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___256_15139.tcenv);
                     delta_level = (uu___256_15139.delta_level);
                     primitive_steps = (uu___256_15139.primitive_steps);
                     strong = (uu___256_15139.strong)
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
                  (fun uu____15168  ->
                     let uu____15169 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15170 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15169
                       uu____15170);
                (let uu____15171 =
                   let uu____15172 = FStar_Syntax_Subst.compress head2 in
                   uu____15172.FStar_Syntax_Syntax.n in
                 match uu____15171 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15190 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15190 with
                      | (uu____15191,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15197 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15205 =
                                   let uu____15206 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15206.FStar_Syntax_Syntax.n in
                                 match uu____15205 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15212,uu____15213))
                                     ->
                                     let uu____15222 =
                                       let uu____15223 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15223.FStar_Syntax_Syntax.n in
                                     (match uu____15222 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15229,msrc,uu____15231))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15240 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15240
                                      | uu____15241 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15242 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15243 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15243 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___257_15248 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___257_15248.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___257_15248.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___257_15248.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15249 = FStar_List.tl stack in
                                    let uu____15250 =
                                      let uu____15251 =
                                        let uu____15254 =
                                          let uu____15255 =
                                            let uu____15268 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15268) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15255 in
                                        FStar_Syntax_Syntax.mk uu____15254 in
                                      uu____15251
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15249 uu____15250
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15284 =
                                      let uu____15285 = is_return body in
                                      match uu____15285 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15289;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15290;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15295 -> false in
                                    if uu____15284
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
                                         let uu____15318 =
                                           let uu____15321 =
                                             let uu____15322 =
                                               let uu____15339 =
                                                 let uu____15342 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15342] in
                                               (uu____15339, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15322 in
                                           FStar_Syntax_Syntax.mk uu____15321 in
                                         uu____15318
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15358 =
                                           let uu____15359 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15359.FStar_Syntax_Syntax.n in
                                         match uu____15358 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15365::uu____15366::[])
                                             ->
                                             let uu____15373 =
                                               let uu____15376 =
                                                 let uu____15377 =
                                                   let uu____15384 =
                                                     let uu____15387 =
                                                       let uu____15388 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15388 in
                                                     let uu____15389 =
                                                       let uu____15392 =
                                                         let uu____15393 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15393 in
                                                       [uu____15392] in
                                                     uu____15387 ::
                                                       uu____15389 in
                                                   (bind1, uu____15384) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15377 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15376 in
                                             uu____15373
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15401 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15407 =
                                           let uu____15410 =
                                             let uu____15411 =
                                               let uu____15426 =
                                                 let uu____15429 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15430 =
                                                   let uu____15433 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15434 =
                                                     let uu____15437 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15438 =
                                                       let uu____15441 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15442 =
                                                         let uu____15445 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15446 =
                                                           let uu____15449 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15449] in
                                                         uu____15445 ::
                                                           uu____15446 in
                                                       uu____15441 ::
                                                         uu____15442 in
                                                     uu____15437 ::
                                                       uu____15438 in
                                                   uu____15433 :: uu____15434 in
                                                 uu____15429 :: uu____15430 in
                                               (bind_inst, uu____15426) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15411 in
                                           FStar_Syntax_Syntax.mk uu____15410 in
                                         uu____15407
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15460  ->
                                            let uu____15461 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15461);
                                       (let uu____15462 = FStar_List.tl stack in
                                        norm cfg env uu____15462 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15486 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15486 with
                      | (uu____15487,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15522 =
                                  let uu____15523 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15523.FStar_Syntax_Syntax.n in
                                match uu____15522 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15529) -> t2
                                | uu____15534 -> head3 in
                              let uu____15535 =
                                let uu____15536 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15536.FStar_Syntax_Syntax.n in
                              match uu____15535 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15542 -> FStar_Pervasives_Native.None in
                            let uu____15543 = maybe_extract_fv head3 in
                            match uu____15543 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15553 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15553
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15558 = maybe_extract_fv head4 in
                                  match uu____15558 with
                                  | FStar_Pervasives_Native.Some uu____15563
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15564 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15569 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15584 =
                              match uu____15584 with
                              | (e,q) ->
                                  let uu____15591 =
                                    let uu____15592 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15592.FStar_Syntax_Syntax.n in
                                  (match uu____15591 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15607 -> false) in
                            let uu____15608 =
                              let uu____15609 =
                                let uu____15616 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15616 :: args in
                              FStar_Util.for_some is_arg_impure uu____15609 in
                            if uu____15608
                            then
                              let uu____15621 =
                                let uu____15622 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15622 in
                              failwith uu____15621
                            else ());
                           (let uu____15624 = maybe_unfold_action head_app in
                            match uu____15624 with
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
                                let uu____15661 = FStar_List.tl stack in
                                norm cfg env uu____15661 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15663) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15687 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15687 in
                     (log cfg
                        (fun uu____15691  ->
                           let uu____15692 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15692);
                      (let uu____15693 = FStar_List.tl stack in
                       norm cfg env uu____15693 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15695) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15820  ->
                               match uu____15820 with
                               | (pat,wopt,tm) ->
                                   let uu____15868 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15868))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____15900 = FStar_List.tl stack in
                     norm cfg env uu____15900 tm
                 | uu____15901 -> fallback ())
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
              (fun uu____15915  ->
                 let uu____15916 = FStar_Ident.string_of_lid msrc in
                 let uu____15917 = FStar_Ident.string_of_lid mtgt in
                 let uu____15918 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15916
                   uu____15917 uu____15918);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____15920 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15920 with
               | (uu____15921,return_repr) ->
                   let return_inst =
                     let uu____15930 =
                       let uu____15931 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15931.FStar_Syntax_Syntax.n in
                     match uu____15930 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15937::[]) ->
                         let uu____15944 =
                           let uu____15947 =
                             let uu____15948 =
                               let uu____15955 =
                                 let uu____15958 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15958] in
                               (return_tm, uu____15955) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15948 in
                           FStar_Syntax_Syntax.mk uu____15947 in
                         uu____15944 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15966 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15969 =
                     let uu____15972 =
                       let uu____15973 =
                         let uu____15988 =
                           let uu____15991 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15992 =
                             let uu____15995 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15995] in
                           uu____15991 :: uu____15992 in
                         (return_inst, uu____15988) in
                       FStar_Syntax_Syntax.Tm_app uu____15973 in
                     FStar_Syntax_Syntax.mk uu____15972 in
                   uu____15969 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16004 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16004 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16007 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16007
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16008;
                     FStar_TypeChecker_Env.mtarget = uu____16009;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16010;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16025;
                     FStar_TypeChecker_Env.mtarget = uu____16026;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16027;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16051 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16052 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16051 t FStar_Syntax_Syntax.tun uu____16052)
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
                (fun uu____16108  ->
                   match uu____16108 with
                   | (a,imp) ->
                       let uu____16119 = norm cfg env [] a in
                       (uu____16119, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___258_16136 = comp1 in
            let uu____16139 =
              let uu____16140 =
                let uu____16149 = norm cfg env [] t in
                let uu____16150 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16149, uu____16150) in
              FStar_Syntax_Syntax.Total uu____16140 in
            {
              FStar_Syntax_Syntax.n = uu____16139;
              FStar_Syntax_Syntax.pos =
                (uu___258_16136.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___258_16136.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___259_16165 = comp1 in
            let uu____16168 =
              let uu____16169 =
                let uu____16178 = norm cfg env [] t in
                let uu____16179 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16178, uu____16179) in
              FStar_Syntax_Syntax.GTotal uu____16169 in
            {
              FStar_Syntax_Syntax.n = uu____16168;
              FStar_Syntax_Syntax.pos =
                (uu___259_16165.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___259_16165.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16231  ->
                      match uu____16231 with
                      | (a,i) ->
                          let uu____16242 = norm cfg env [] a in
                          (uu____16242, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___208_16253  ->
                      match uu___208_16253 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16257 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16257
                      | f -> f)) in
            let uu___260_16261 = comp1 in
            let uu____16264 =
              let uu____16265 =
                let uu___261_16266 = ct in
                let uu____16267 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16268 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16271 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16267;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___261_16266.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16268;
                  FStar_Syntax_Syntax.effect_args = uu____16271;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16265 in
            {
              FStar_Syntax_Syntax.n = uu____16264;
              FStar_Syntax_Syntax.pos =
                (uu___260_16261.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___260_16261.FStar_Syntax_Syntax.vars)
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
            (let uu___262_16289 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___262_16289.tcenv);
               delta_level = (uu___262_16289.delta_level);
               primitive_steps = (uu___262_16289.primitive_steps);
               strong = (uu___262_16289.strong)
             }) env [] t in
        let non_info t =
          let uu____16294 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16294 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16297 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___263_16316 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___263_16316.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___263_16316.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16323 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16323
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
                    let uu___264_16334 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___264_16334.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___264_16334.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___264_16334.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags1
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___265_16336 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___265_16336.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___265_16336.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___265_16336.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___265_16336.FStar_Syntax_Syntax.flags)
                    } in
              let uu___266_16337 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___266_16337.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___266_16337.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16339 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16342  ->
        match uu____16342 with
        | (x,imp) ->
            let uu____16345 =
              let uu___267_16346 = x in
              let uu____16347 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___267_16346.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___267_16346.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16347
              } in
            (uu____16345, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16353 =
          FStar_List.fold_left
            (fun uu____16371  ->
               fun b  ->
                 match uu____16371 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16353 with | (nbs,uu____16411) -> FStar_List.rev nbs
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
            let uu____16427 =
              let uu___268_16428 = rc in
              let uu____16429 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___268_16428.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16429;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___268_16428.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16427
        | uu____16436 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16449  ->
               let uu____16450 = FStar_Syntax_Print.tag_of_term t in
               let uu____16451 = FStar_Syntax_Print.term_to_string t in
               let uu____16452 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16459 =
                 let uu____16460 =
                   let uu____16463 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16463 in
                 stack_to_string uu____16460 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16450 uu____16451 uu____16452 uu____16459);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16492 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16492
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16494 =
                     let uu____16495 =
                       let uu____16496 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16496 in
                     FStar_Util.string_of_int uu____16495 in
                   let uu____16501 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16502 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16494 uu____16501 uu____16502
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16548  ->
                     let uu____16549 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16549);
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
               let uu____16585 =
                 let uu___269_16586 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___269_16586.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___269_16586.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16585
           | (Arg (Univ uu____16587,uu____16588,uu____16589))::uu____16590 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16593,uu____16594))::uu____16595 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16611),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16664  ->
                     let uu____16665 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16665);
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
                  (let uu____16675 = FStar_ST.op_Bang m in
                   match uu____16675 with
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
                   | FStar_Pervasives_Native.Some (uu____16821,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16868 =
                 log cfg
                   (fun uu____16872  ->
                      let uu____16873 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16873);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16877 =
                 let uu____16878 = FStar_Syntax_Subst.compress t in
                 uu____16878.FStar_Syntax_Syntax.n in
               (match uu____16877 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16905 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16905 in
                    (log cfg
                       (fun uu____16909  ->
                          let uu____16910 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16910);
                     (let uu____16911 = FStar_List.tl stack in
                      norm cfg env1 uu____16911 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16912);
                       FStar_Syntax_Syntax.pos = uu____16913;
                       FStar_Syntax_Syntax.vars = uu____16914;_},(e,uu____16916)::[])
                    -> norm cfg env1 stack' e
                | uu____16945 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16956 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16956
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16968  ->
                     let uu____16969 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16969);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16974 =
                   log cfg
                     (fun uu____16979  ->
                        let uu____16980 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16981 =
                          let uu____16982 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16999  ->
                                    match uu____16999 with
                                    | (p,uu____17009,uu____17010) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16982
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16980 uu____16981);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___209_17027  ->
                                match uu___209_17027 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17028 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___270_17032 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___270_17032.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___270_17032.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17064 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17085 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17145  ->
                                    fun uu____17146  ->
                                      match (uu____17145, uu____17146) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17237 = norm_pat env3 p1 in
                                          (match uu____17237 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17085 with
                           | (pats1,env3) ->
                               ((let uu___271_17319 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___271_17319.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___272_17338 = x in
                            let uu____17339 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___272_17338.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___272_17338.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17339
                            } in
                          ((let uu___273_17353 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___273_17353.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___274_17364 = x in
                            let uu____17365 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___274_17364.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___274_17364.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17365
                            } in
                          ((let uu___275_17379 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___275_17379.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___276_17395 = x in
                            let uu____17396 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___276_17395.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___276_17395.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17396
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___277_17403 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___277_17403.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17413 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17427 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17427 with
                                  | (p,wopt,e) ->
                                      let uu____17447 = norm_pat env1 p in
                                      (match uu____17447 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17472 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17472 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17478 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17478) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17488) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17493 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17494;
                         FStar_Syntax_Syntax.fv_delta = uu____17495;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17496;
                         FStar_Syntax_Syntax.fv_delta = uu____17497;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17498);_}
                       -> true
                   | uu____17505 -> false in
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
                   let uu____17650 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17650 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17737 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17776 ->
                                 let uu____17777 =
                                   let uu____17778 = is_cons head1 in
                                   Prims.op_Negation uu____17778 in
                                 FStar_Util.Inr uu____17777)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17803 =
                              let uu____17804 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17804.FStar_Syntax_Syntax.n in
                            (match uu____17803 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17822 ->
                                 let uu____17823 =
                                   let uu____17824 = is_cons head1 in
                                   Prims.op_Negation uu____17824 in
                                 FStar_Util.Inr uu____17823))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17893)::rest_a,(p1,uu____17896)::rest_p) ->
                       let uu____17940 = matches_pat t1 p1 in
                       (match uu____17940 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17989 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18095 = matches_pat scrutinee1 p1 in
                       (match uu____18095 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18135  ->
                                  let uu____18136 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18137 =
                                    let uu____18138 =
                                      FStar_List.map
                                        (fun uu____18148  ->
                                           match uu____18148 with
                                           | (uu____18153,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18138
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18136 uu____18137);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18184  ->
                                       match uu____18184 with
                                       | (bv,t1) ->
                                           let uu____18207 =
                                             let uu____18214 =
                                               let uu____18217 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18217 in
                                             let uu____18218 =
                                               let uu____18219 =
                                                 let uu____18250 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18250, false) in
                                               Clos uu____18219 in
                                             (uu____18214, uu____18218) in
                                           uu____18207 :: env2) env1 s in
                              let uu____18359 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18359))) in
                 let uu____18360 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18360
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___210_18381  ->
                match uu___210_18381 with
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
            let uu___278_18416 = config s e in
            {
              steps = (uu___278_18416.steps);
              tcenv = (uu___278_18416.tcenv);
              delta_level = (uu___278_18416.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___278_18416.strong)
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
      fun t  -> let uu____18441 = config s e in norm_comp uu____18441 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18454 = config [] env in norm_universe uu____18454 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18467 = config [] env in ghost_to_pure_aux uu____18467 [] c
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
        let uu____18485 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18485 in
      let uu____18492 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18492
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___279_18494 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___279_18494.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___279_18494.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18497  ->
                    let uu____18498 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18498))
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
            ((let uu____18515 =
                let uu____18520 =
                  let uu____18521 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18521 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18520) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18515);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18532 = config [AllowUnboundUniverses] env in
          norm_comp uu____18532 [] c
        with
        | e ->
            ((let uu____18545 =
                let uu____18550 =
                  let uu____18551 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18551 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18550) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18545);
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
                   let uu____18588 =
                     let uu____18589 =
                       let uu____18596 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18596) in
                     FStar_Syntax_Syntax.Tm_refine uu____18589 in
                   mk uu____18588 t01.FStar_Syntax_Syntax.pos
               | uu____18601 -> t2)
          | uu____18602 -> t2 in
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
        let uu____18642 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18642 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18671 ->
                 let uu____18678 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18678 with
                  | (actuals,uu____18688,uu____18689) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18703 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18703 with
                         | (binders,args) ->
                             let uu____18720 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18720
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
      | uu____18728 ->
          let uu____18729 = FStar_Syntax_Util.head_and_args t in
          (match uu____18729 with
           | (head1,args) ->
               let uu____18766 =
                 let uu____18767 = FStar_Syntax_Subst.compress head1 in
                 uu____18767.FStar_Syntax_Syntax.n in
               (match uu____18766 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18770,thead) ->
                    let uu____18796 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18796 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18838 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___284_18846 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___284_18846.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___284_18846.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___284_18846.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___284_18846.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___284_18846.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___284_18846.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___284_18846.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___284_18846.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___284_18846.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___284_18846.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___284_18846.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___284_18846.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___284_18846.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___284_18846.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___284_18846.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___284_18846.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___284_18846.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___284_18846.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___284_18846.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___284_18846.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___284_18846.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___284_18846.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___284_18846.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___284_18846.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___284_18846.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___284_18846.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___284_18846.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___284_18846.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___284_18846.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___284_18846.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___284_18846.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18838 with
                            | (uu____18847,ty,uu____18849) ->
                                eta_expand_with_type env t ty))
                | uu____18850 ->
                    let uu____18851 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___285_18859 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___285_18859.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___285_18859.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___285_18859.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___285_18859.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___285_18859.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___285_18859.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___285_18859.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___285_18859.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___285_18859.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___285_18859.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___285_18859.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___285_18859.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___285_18859.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___285_18859.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___285_18859.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___285_18859.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___285_18859.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___285_18859.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___285_18859.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___285_18859.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___285_18859.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___285_18859.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___285_18859.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___285_18859.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___285_18859.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___285_18859.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___285_18859.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___285_18859.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___285_18859.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___285_18859.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___285_18859.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18851 with
                     | (uu____18860,ty,uu____18862) ->
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
            | (uu____18936,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18942,FStar_Util.Inl t) ->
                let uu____18948 =
                  let uu____18951 =
                    let uu____18952 =
                      let uu____18965 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18965) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18952 in
                  FStar_Syntax_Syntax.mk uu____18951 in
                uu____18948 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18969 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18969 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18996 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19051 ->
                    let uu____19052 =
                      let uu____19061 =
                        let uu____19062 = FStar_Syntax_Subst.compress t3 in
                        uu____19062.FStar_Syntax_Syntax.n in
                      (uu____19061, tc) in
                    (match uu____19052 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19087) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19124) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19163,FStar_Util.Inl uu____19164) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19187 -> failwith "Impossible") in
              (match uu____18996 with
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
          let uu____19292 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19292 with
          | (univ_names1,binders1,tc) ->
              let uu____19350 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19350)
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
          let uu____19385 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19385 with
          | (univ_names1,binders1,tc) ->
              let uu____19445 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19445)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19478 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19478 with
           | (univ_names1,binders1,typ1) ->
               let uu___286_19506 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___286_19506.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___286_19506.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___286_19506.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___286_19506.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___287_19527 = s in
          let uu____19528 =
            let uu____19529 =
              let uu____19538 = FStar_List.map (elim_uvars env) sigs in
              (uu____19538, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19529 in
          {
            FStar_Syntax_Syntax.sigel = uu____19528;
            FStar_Syntax_Syntax.sigrng =
              (uu___287_19527.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___287_19527.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___287_19527.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___287_19527.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19555 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19555 with
           | (univ_names1,uu____19573,typ1) ->
               let uu___288_19587 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___288_19587.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___288_19587.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___288_19587.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___288_19587.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19593 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19593 with
           | (univ_names1,uu____19611,typ1) ->
               let uu___289_19625 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___289_19625.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___289_19625.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___289_19625.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___289_19625.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19659 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19659 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19682 =
                            let uu____19683 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19683 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19682 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___290_19686 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___290_19686.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___290_19686.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___291_19687 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___291_19687.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___291_19687.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___291_19687.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___291_19687.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___292_19699 = s in
          let uu____19700 =
            let uu____19701 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19701 in
          {
            FStar_Syntax_Syntax.sigel = uu____19700;
            FStar_Syntax_Syntax.sigrng =
              (uu___292_19699.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___292_19699.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___292_19699.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___292_19699.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19705 = elim_uvars_aux_t env us [] t in
          (match uu____19705 with
           | (us1,uu____19723,t1) ->
               let uu___293_19737 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___293_19737.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___293_19737.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___293_19737.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___293_19737.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19738 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19740 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19740 with
           | (univs1,binders,signature) ->
               let uu____19768 =
                 let uu____19777 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19777 with
                 | (univs_opening,univs2) ->
                     let uu____19804 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19804) in
               (match uu____19768 with
                | (univs_opening,univs_closing) ->
                    let uu____19821 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19827 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19828 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19827, uu____19828) in
                    (match uu____19821 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19850 =
                           match uu____19850 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19868 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19868 with
                                | (us1,t1) ->
                                    let uu____19879 =
                                      let uu____19884 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19891 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19884, uu____19891) in
                                    (match uu____19879 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19904 =
                                           let uu____19909 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19918 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19909, uu____19918) in
                                         (match uu____19904 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19934 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19934 in
                                              let uu____19935 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19935 with
                                               | (uu____19956,uu____19957,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19972 =
                                                       let uu____19973 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19973 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19972 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19978 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19978 with
                           | (uu____19991,uu____19992,t1) -> t1 in
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
                             | uu____20052 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20069 =
                               let uu____20070 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20070.FStar_Syntax_Syntax.n in
                             match uu____20069 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20129 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20158 =
                               let uu____20159 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20159.FStar_Syntax_Syntax.n in
                             match uu____20158 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20180) ->
                                 let uu____20201 = destruct_action_body body in
                                 (match uu____20201 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20246 ->
                                 let uu____20247 = destruct_action_body t in
                                 (match uu____20247 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20296 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20296 with
                           | (action_univs,t) ->
                               let uu____20305 = destruct_action_typ_templ t in
                               (match uu____20305 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___294_20346 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___294_20346.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___294_20346.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___295_20348 = ed in
                           let uu____20349 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20350 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20351 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20352 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20353 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20354 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20355 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20356 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20357 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20358 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20359 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20360 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20361 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20362 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___295_20348.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___295_20348.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20349;
                             FStar_Syntax_Syntax.bind_wp = uu____20350;
                             FStar_Syntax_Syntax.if_then_else = uu____20351;
                             FStar_Syntax_Syntax.ite_wp = uu____20352;
                             FStar_Syntax_Syntax.stronger = uu____20353;
                             FStar_Syntax_Syntax.close_wp = uu____20354;
                             FStar_Syntax_Syntax.assert_p = uu____20355;
                             FStar_Syntax_Syntax.assume_p = uu____20356;
                             FStar_Syntax_Syntax.null_wp = uu____20357;
                             FStar_Syntax_Syntax.trivial = uu____20358;
                             FStar_Syntax_Syntax.repr = uu____20359;
                             FStar_Syntax_Syntax.return_repr = uu____20360;
                             FStar_Syntax_Syntax.bind_repr = uu____20361;
                             FStar_Syntax_Syntax.actions = uu____20362
                           } in
                         let uu___296_20365 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___296_20365.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___296_20365.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___296_20365.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___296_20365.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___211_20382 =
            match uu___211_20382 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20409 = elim_uvars_aux_t env us [] t in
                (match uu____20409 with
                 | (us1,uu____20433,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___297_20452 = sub_eff in
            let uu____20453 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20456 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___297_20452.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___297_20452.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20453;
              FStar_Syntax_Syntax.lift = uu____20456
            } in
          let uu___298_20459 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___298_20459.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___298_20459.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___298_20459.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___298_20459.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20469 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20469 with
           | (univ_names1,binders1,comp1) ->
               let uu___299_20503 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___299_20503.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___299_20503.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___299_20503.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___299_20503.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20514 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t