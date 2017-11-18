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
  fun uu___189_497  ->
    match uu___189_497 with
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
      | FStar_Pervasives_Native.Some uu____1263 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1335 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1335 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___190_1342  ->
    match uu___190_1342 with
    | Arg (c,uu____1344,uu____1345) ->
        let uu____1346 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1346
    | MemoLazy uu____1347 -> "MemoLazy"
    | Abs (uu____1354,bs,uu____1356,uu____1357,uu____1358) ->
        let uu____1363 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1363
    | UnivArgs uu____1368 -> "UnivArgs"
    | Match uu____1375 -> "Match"
    | App (uu____1382,t,uu____1384,uu____1385) ->
        let uu____1386 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1386
    | Meta (m,uu____1388) -> "Meta"
    | Let uu____1389 -> "Let"
    | Cfg uu____1398 -> "Cfg"
    | Debug (t,uu____1400) ->
        let uu____1401 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1401
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1409 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1409 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1425 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1425 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1438 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1438 then f () else ()
let is_empty: 'Auu____1442 . 'Auu____1442 Prims.list -> Prims.bool =
  fun uu___191_1448  ->
    match uu___191_1448 with | [] -> true | uu____1451 -> false
let lookup_bvar:
  'Auu____1458 'Auu____1459 .
    ('Auu____1459,'Auu____1458) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1458
  =
  fun env  ->
    fun x  ->
      try
        let uu____1483 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1483
      with
      | uu____1496 ->
          let uu____1497 =
            let uu____1498 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1498 in
          failwith uu____1497
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
          let uu____1535 =
            FStar_List.fold_left
              (fun uu____1561  ->
                 fun u1  ->
                   match uu____1561 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1586 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1586 with
                        | (k_u,n1) ->
                            let uu____1601 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1601
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1535 with
          | (uu____1619,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1644 =
                   let uu____1645 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1645 in
                 match uu____1644 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1663 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1672 ->
                   let uu____1673 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1673
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1679 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1688 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1697 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1704 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1704 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1721 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1721 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1729 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1737 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1737 with
                                  | (uu____1742,m) -> n1 <= m)) in
                        if uu____1729 then rest1 else us1
                    | uu____1747 -> us1)
               | uu____1752 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1756 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1756 in
        let uu____1759 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1759
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1761 = aux u in
           match uu____1761 with
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
          (fun uu____1865  ->
             let uu____1866 = FStar_Syntax_Print.tag_of_term t in
             let uu____1867 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1866
               uu____1867);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1874 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1876 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1901 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1902 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1903 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1904 ->
                  let uu____1921 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1921
                  then
                    let uu____1922 =
                      let uu____1923 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1924 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1923 uu____1924 in
                    failwith uu____1922
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1927 =
                    let uu____1928 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1928 in
                  mk uu____1927 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1935 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1935
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1937 = lookup_bvar env x in
                  (match uu____1937 with
                   | Univ uu____1940 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1944) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2056 = closures_as_binders_delayed cfg env bs in
                  (match uu____2056 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2084 =
                         let uu____2085 =
                           let uu____2102 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2102) in
                         FStar_Syntax_Syntax.Tm_abs uu____2085 in
                       mk uu____2084 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2133 = closures_as_binders_delayed cfg env bs in
                  (match uu____2133 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2175 =
                    let uu____2186 =
                      let uu____2193 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2193] in
                    closures_as_binders_delayed cfg env uu____2186 in
                  (match uu____2175 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2211 =
                         let uu____2212 =
                           let uu____2219 =
                             let uu____2220 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2220
                               FStar_Pervasives_Native.fst in
                           (uu____2219, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2212 in
                       mk uu____2211 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2311 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2311
                    | FStar_Util.Inr c ->
                        let uu____2325 = close_comp cfg env c in
                        FStar_Util.Inr uu____2325 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2341 =
                    let uu____2342 =
                      let uu____2369 = closure_as_term_delayed cfg env t11 in
                      (uu____2369, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2342 in
                  mk uu____2341 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2420 =
                    let uu____2421 =
                      let uu____2428 = closure_as_term_delayed cfg env t' in
                      let uu____2431 =
                        let uu____2432 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2432 in
                      (uu____2428, uu____2431) in
                    FStar_Syntax_Syntax.Tm_meta uu____2421 in
                  mk uu____2420 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2492 =
                    let uu____2493 =
                      let uu____2500 = closure_as_term_delayed cfg env t' in
                      let uu____2503 =
                        let uu____2504 =
                          let uu____2511 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2511) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2504 in
                      (uu____2500, uu____2503) in
                    FStar_Syntax_Syntax.Tm_meta uu____2493 in
                  mk uu____2492 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2530 =
                    let uu____2531 =
                      let uu____2538 = closure_as_term_delayed cfg env t' in
                      let uu____2541 =
                        let uu____2542 =
                          let uu____2551 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2551) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2542 in
                      (uu____2538, uu____2541) in
                    FStar_Syntax_Syntax.Tm_meta uu____2531 in
                  mk uu____2530 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2564 =
                    let uu____2565 =
                      let uu____2572 = closure_as_term_delayed cfg env t' in
                      (uu____2572, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2565 in
                  mk uu____2564 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2612  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2631 =
                    let uu____2642 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2642
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2661 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___210_2673 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___210_2673.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___210_2673.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2661)) in
                  (match uu____2631 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___211_2689 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___211_2689.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___211_2689.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2700,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2759  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2784 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2784
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2804  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2826 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2826
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___212_2838 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___212_2838.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___212_2838.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___213_2839 = lb in
                    let uu____2840 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___213_2839.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___213_2839.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2840
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2870  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2959 =
                    match uu____2959 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3014 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3035 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3095  ->
                                        fun uu____3096  ->
                                          match (uu____3095, uu____3096) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3187 =
                                                norm_pat env3 p1 in
                                              (match uu____3187 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3035 with
                               | (pats1,env3) ->
                                   ((let uu___214_3269 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___214_3269.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___215_3288 = x in
                                let uu____3289 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___215_3288.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___215_3288.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3289
                                } in
                              ((let uu___216_3303 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___216_3303.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___217_3314 = x in
                                let uu____3315 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___217_3314.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___217_3314.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3315
                                } in
                              ((let uu___218_3329 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___218_3329.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___219_3345 = x in
                                let uu____3346 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___219_3345.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___219_3345.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3346
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___220_3353 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___220_3353.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3356 = norm_pat env1 pat in
                        (match uu____3356 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3385 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3385 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3391 =
                    let uu____3392 =
                      let uu____3415 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3415) in
                    FStar_Syntax_Syntax.Tm_match uu____3392 in
                  mk uu____3391 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3501 -> closure_as_term cfg env t
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
        | uu____3527 ->
            FStar_List.map
              (fun uu____3544  ->
                 match uu____3544 with
                 | (x,imp) ->
                     let uu____3563 = closure_as_term_delayed cfg env x in
                     (uu____3563, imp)) args
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
        let uu____3577 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3626  ->
                  fun uu____3627  ->
                    match (uu____3626, uu____3627) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___221_3697 = b in
                          let uu____3698 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___221_3697.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___221_3697.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3698
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3577 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3791 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3804 = closure_as_term_delayed cfg env t in
                 let uu____3805 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3804 uu____3805
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3818 = closure_as_term_delayed cfg env t in
                 let uu____3819 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3818 uu____3819
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
                        (fun uu___192_3845  ->
                           match uu___192_3845 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3849 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3849
                           | f -> f)) in
                 let uu____3853 =
                   let uu___222_3854 = c1 in
                   let uu____3855 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3855;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___222_3854.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3853)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___193_3865  ->
            match uu___193_3865 with
            | FStar_Syntax_Syntax.DECREASES uu____3866 -> false
            | uu____3869 -> true))
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
                   (fun uu___194_3887  ->
                      match uu___194_3887 with
                      | FStar_Syntax_Syntax.DECREASES uu____3888 -> false
                      | uu____3891 -> true)) in
            let rc1 =
              let uu___223_3893 = rc in
              let uu____3894 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___223_3893.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3894;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3901 -> lopt
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
    let uu____3991 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3991 in
  let arg_as_bounded_int uu____4019 =
    match uu____4019 with
    | (a,uu____4031) ->
        let uu____4038 =
          let uu____4039 = FStar_Syntax_Subst.compress a in
          uu____4039.FStar_Syntax_Syntax.n in
        (match uu____4038 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4049;
                FStar_Syntax_Syntax.vars = uu____4050;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4052;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4053;_},uu____4054)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4093 =
               let uu____4098 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4098) in
             FStar_Pervasives_Native.Some uu____4093
         | uu____4103 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4145 = f a in FStar_Pervasives_Native.Some uu____4145
    | uu____4146 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4196 = f a0 a1 in FStar_Pervasives_Native.Some uu____4196
    | uu____4197 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4246 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4246 in
  let binary_op as_a f res args =
    let uu____4302 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4302 in
  let as_primitive_step uu____4326 =
    match uu____4326 with
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
           let uu____4374 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4374) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4402 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____4402) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4423 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____4423) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4451 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____4451) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4479 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____4479) in
  let list_of_string' rng s =
    let name l =
      let uu____4493 =
        let uu____4494 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4494 in
      mk uu____4493 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4504 =
      let uu____4507 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4507 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4504 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4539 =
      let uu____4540 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4540 in
    FStar_Syntax_Embeddings.embed_int rng uu____4539 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4558 = arg_as_string a1 in
        (match uu____4558 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4564 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____4564 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4577 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4577
              | uu____4578 -> FStar_Pervasives_Native.None)
         | uu____4583 -> FStar_Pervasives_Native.None)
    | uu____4586 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4596 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4596 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4620 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4631 =
          let uu____4652 = arg_as_string fn in
          let uu____4655 = arg_as_int from_line in
          let uu____4658 = arg_as_int from_col in
          let uu____4661 = arg_as_int to_line in
          let uu____4664 = arg_as_int to_col in
          (uu____4652, uu____4655, uu____4658, uu____4661, uu____4664) in
        (match uu____4631 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4695 =
                 let uu____4696 = FStar_BigInt.to_int_fs from_l in
                 let uu____4697 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4696 uu____4697 in
               let uu____4698 =
                 let uu____4699 = FStar_BigInt.to_int_fs to_l in
                 let uu____4700 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4699 uu____4700 in
               FStar_Range.mk_range fn1 uu____4695 uu____4698 in
             let uu____4701 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4701
         | uu____4706 -> FStar_Pervasives_Native.None)
    | uu____4727 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4754)::(a1,uu____4756)::(a2,uu____4758)::[] ->
        let uu____4795 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4795 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4808 -> FStar_Pervasives_Native.None)
    | uu____4809 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4836)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4845 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____4869 =
      let uu____4884 =
        let uu____4899 =
          let uu____4914 =
            let uu____4929 =
              let uu____4944 =
                let uu____4959 =
                  let uu____4974 =
                    let uu____4989 =
                      let uu____5004 =
                        let uu____5019 =
                          let uu____5034 =
                            let uu____5049 =
                              let uu____5064 =
                                let uu____5079 =
                                  let uu____5094 =
                                    let uu____5109 =
                                      let uu____5124 =
                                        let uu____5139 =
                                          let uu____5154 =
                                            let uu____5167 =
                                              FStar_Parser_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____5167,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____5174 =
                                            let uu____5189 =
                                              let uu____5202 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____5202,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list
                                                      FStar_Syntax_Embeddings.unembed_char_safe)
                                                   string_of_list')) in
                                            let uu____5213 =
                                              let uu____5228 =
                                                let uu____5243 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____5243,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              let uu____5252 =
                                                let uu____5269 =
                                                  let uu____5284 =
                                                    FStar_Parser_Const.p2l
                                                      ["Prims"; "mk_range"] in
                                                  (uu____5284,
                                                    (Prims.parse_int "5"),
                                                    mk_range1) in
                                                let uu____5293 =
                                                  let uu____5310 =
                                                    let uu____5329 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "Range";
                                                        "prims_to_fstar_range"] in
                                                    (uu____5329,
                                                      (Prims.parse_int "1"),
                                                      idstep) in
                                                  [uu____5310] in
                                                uu____5269 :: uu____5293 in
                                              uu____5228 :: uu____5252 in
                                            uu____5189 :: uu____5213 in
                                          uu____5154 :: uu____5174 in
                                        (FStar_Parser_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____5139 in
                                      (FStar_Parser_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____5124 in
                                    (FStar_Parser_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____5109 in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool1))
                                    :: uu____5094 in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int1)) ::
                                  uu____5079 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5064 in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5049 in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5034 in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5019 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5004 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5665 = FStar_BigInt.ge_big_int x y in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5665)))
                      :: uu____4989 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5691 = FStar_BigInt.gt_big_int x y in
                              FStar_Syntax_Embeddings.embed_bool r uu____5691)))
                    :: uu____4974 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5717 = FStar_BigInt.le_big_int x y in
                            FStar_Syntax_Embeddings.embed_bool r uu____5717)))
                  :: uu____4959 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____5743 = FStar_BigInt.lt_big_int x y in
                          FStar_Syntax_Embeddings.embed_bool r uu____5743)))
                :: uu____4944 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____4929 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____4914 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____4899 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____4884 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____4869 in
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
      let uu____5893 =
        let uu____5894 =
          let uu____5895 = FStar_Syntax_Syntax.as_arg c in [uu____5895] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____5894 in
      uu____5893 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____5930 =
              let uu____5943 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____5943, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____5963  ->
                        fun uu____5964  ->
                          match (uu____5963, uu____5964) with
                          | ((int_to_t1,x),(uu____5983,y)) ->
                              let uu____5993 = FStar_BigInt.add_big_int x y in
                              int_as_bounded r int_to_t1 uu____5993))) in
            let uu____5994 =
              let uu____6009 =
                let uu____6022 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6022, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6042  ->
                          fun uu____6043  ->
                            match (uu____6042, uu____6043) with
                            | ((int_to_t1,x),(uu____6062,y)) ->
                                let uu____6072 = FStar_BigInt.sub_big_int x y in
                                int_as_bounded r int_to_t1 uu____6072))) in
              let uu____6073 =
                let uu____6088 =
                  let uu____6101 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6101, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6121  ->
                            fun uu____6122  ->
                              match (uu____6121, uu____6122) with
                              | ((int_to_t1,x),(uu____6141,y)) ->
                                  let uu____6151 =
                                    FStar_BigInt.mult_big_int x y in
                                  int_as_bounded r int_to_t1 uu____6151))) in
                [uu____6088] in
              uu____6009 :: uu____6073 in
            uu____5930 :: uu____5994)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6241)::(a1,uu____6243)::(a2,uu____6245)::[] ->
        let uu____6282 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6282 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6288 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6288.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6288.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___225_6292 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___225_6292.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___225_6292.FStar_Syntax_Syntax.vars)
                })
         | uu____6293 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6295)::uu____6296::(a1,uu____6298)::(a2,uu____6300)::[] ->
        let uu____6349 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6349 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___224_6355 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___224_6355.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___224_6355.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___225_6359 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___225_6359.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___225_6359.FStar_Syntax_Syntax.vars)
                })
         | uu____6360 -> FStar_Pervasives_Native.None)
    | uu____6361 -> failwith "Unexpected number of arguments" in
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
      let uu____6380 =
        let uu____6381 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6381 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6380
    with | uu____6387 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6391 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6391) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6451  ->
           fun subst1  ->
             match uu____6451 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____6493)) ->
                      let uu____6552 = b in
                      (match uu____6552 with
                       | (bv,uu____6560) ->
                           let uu____6561 =
                             let uu____6562 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6562 in
                           if uu____6561
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6567 = unembed_binder term1 in
                              match uu____6567 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6574 =
                                      let uu___228_6575 = bv in
                                      let uu____6576 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___228_6575.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___228_6575.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6576
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6574 in
                                  let b_for_x =
                                    let uu____6580 =
                                      let uu____6587 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6587) in
                                    FStar_Syntax_Syntax.NT uu____6580 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___195_6596  ->
                                         match uu___195_6596 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6597,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6599;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6600;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6605 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6606 -> subst1)) env []
let reduce_primops:
  'Auu____6623 'Auu____6624 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6624) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6623 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6665 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6665
          then tm
          else
            (let uu____6667 = FStar_Syntax_Util.head_and_args tm in
             match uu____6667 with
             | (head1,args) ->
                 let uu____6704 =
                   let uu____6705 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6705.FStar_Syntax_Syntax.n in
                 (match uu____6704 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6709 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6709 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6726  ->
                                   let uu____6727 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6728 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6735 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6727 uu____6728 uu____6735);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6740  ->
                                   let uu____6741 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6741);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6744  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6746 =
                                 prim_step.interpretation psc args in
                               match uu____6746 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6752  ->
                                         let uu____6753 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6753);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6759  ->
                                         let uu____6760 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6761 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6760 uu____6761);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6762 ->
                           (log_primops cfg
                              (fun uu____6766  ->
                                 let uu____6767 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6767);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6771  ->
                            let uu____6772 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6772);
                       (match args with
                        | (a1,uu____6774)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6791 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6803  ->
                            let uu____6804 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6804);
                       (match args with
                        | (t,uu____6806)::(r,uu____6808)::[] ->
                            let uu____6835 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____6835 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___229_6839 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___229_6839.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___229_6839.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6842 -> tm))
                  | uu____6851 -> tm))
let reduce_equality:
  'Auu____6856 'Auu____6857 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6857) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6856 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___230_6895 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___230_6895.tcenv);
           delta_level = (uu___230_6895.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___230_6895.strong)
         }) tm
let maybe_simplify:
  'Auu____6902 'Auu____6903 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6903) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6902 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____6945 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____6945
          then tm1
          else
            (let w t =
               let uu___231_6957 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___231_6957.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___231_6957.FStar_Syntax_Syntax.vars)
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
               | uu____6974 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7014;
                         FStar_Syntax_Syntax.vars = uu____7015;_},uu____7016);
                    FStar_Syntax_Syntax.pos = uu____7017;
                    FStar_Syntax_Syntax.vars = uu____7018;_},args)
                 ->
                 let uu____7044 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7044
                 then
                   let uu____7045 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7045 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7100)::
                        (uu____7101,(arg,uu____7103))::[] -> arg
                    | (uu____7168,(arg,uu____7170))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7171)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7236)::uu____7237::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7300::(FStar_Pervasives_Native.Some (false
                                   ),uu____7301)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7364 -> tm1)
                 else
                   (let uu____7380 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7380
                    then
                      let uu____7381 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7381 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7436)::uu____7437::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7500::(FStar_Pervasives_Native.Some (true
                                     ),uu____7501)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7564)::
                          (uu____7565,(arg,uu____7567))::[] -> arg
                      | (uu____7632,(arg,uu____7634))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7635)::[]
                          -> arg
                      | uu____7700 -> tm1
                    else
                      (let uu____7716 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____7716
                       then
                         let uu____7717 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____7717 with
                         | uu____7772::(FStar_Pervasives_Native.Some (true
                                        ),uu____7773)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____7836)::uu____7837::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____7900)::
                             (uu____7901,(arg,uu____7903))::[] -> arg
                         | (uu____7968,(p,uu____7970))::(uu____7971,(q,uu____7973))::[]
                             ->
                             let uu____8038 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8038
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8040 -> tm1
                       else
                         (let uu____8056 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8056
                          then
                            let uu____8057 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8057 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8112)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8151)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8190 -> tm1
                          else
                            (let uu____8206 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8206
                             then
                               match args with
                               | (t,uu____8208)::[] ->
                                   let uu____8225 =
                                     let uu____8226 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8226.FStar_Syntax_Syntax.n in
                                   (match uu____8225 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8229::[],body,uu____8231) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8258 -> tm1)
                                    | uu____8261 -> tm1)
                               | (uu____8262,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8263))::
                                   (t,uu____8265)::[] ->
                                   let uu____8304 =
                                     let uu____8305 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8305.FStar_Syntax_Syntax.n in
                                   (match uu____8304 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8308::[],body,uu____8310) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8337 -> tm1)
                                    | uu____8340 -> tm1)
                               | uu____8341 -> tm1
                             else
                               (let uu____8351 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8351
                                then
                                  match args with
                                  | (t,uu____8353)::[] ->
                                      let uu____8370 =
                                        let uu____8371 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8371.FStar_Syntax_Syntax.n in
                                      (match uu____8370 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8374::[],body,uu____8376)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8403 -> tm1)
                                       | uu____8406 -> tm1)
                                  | (uu____8407,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8408))::(t,uu____8410)::[] ->
                                      let uu____8449 =
                                        let uu____8450 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8450.FStar_Syntax_Syntax.n in
                                      (match uu____8449 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8453::[],body,uu____8455)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8482 -> tm1)
                                       | uu____8485 -> tm1)
                                  | uu____8486 -> tm1
                                else
                                  (let uu____8496 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8496
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8497;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8498;_},uu____8499)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8516;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8517;_},uu____8518)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8535 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8546;
                    FStar_Syntax_Syntax.vars = uu____8547;_},args)
                 ->
                 let uu____8569 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8569
                 then
                   let uu____8570 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8570 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8625)::
                        (uu____8626,(arg,uu____8628))::[] -> arg
                    | (uu____8693,(arg,uu____8695))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8696)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8761)::uu____8762::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8825::(FStar_Pervasives_Native.Some (false
                                   ),uu____8826)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8889 -> tm1)
                 else
                   (let uu____8905 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8905
                    then
                      let uu____8906 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8906 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8961)::uu____8962::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9025::(FStar_Pervasives_Native.Some (true
                                     ),uu____9026)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9089)::
                          (uu____9090,(arg,uu____9092))::[] -> arg
                      | (uu____9157,(arg,uu____9159))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9160)::[]
                          -> arg
                      | uu____9225 -> tm1
                    else
                      (let uu____9241 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9241
                       then
                         let uu____9242 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9242 with
                         | uu____9297::(FStar_Pervasives_Native.Some (true
                                        ),uu____9298)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9361)::uu____9362::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9425)::
                             (uu____9426,(arg,uu____9428))::[] -> arg
                         | (uu____9493,(p,uu____9495))::(uu____9496,(q,uu____9498))::[]
                             ->
                             let uu____9563 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9563
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9565 -> tm1
                       else
                         (let uu____9581 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9581
                          then
                            let uu____9582 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9582 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9637)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9676)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9715 -> tm1
                          else
                            (let uu____9731 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9731
                             then
                               match args with
                               | (t,uu____9733)::[] ->
                                   let uu____9750 =
                                     let uu____9751 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9751.FStar_Syntax_Syntax.n in
                                   (match uu____9750 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9754::[],body,uu____9756) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9783 -> tm1)
                                    | uu____9786 -> tm1)
                               | (uu____9787,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9788))::
                                   (t,uu____9790)::[] ->
                                   let uu____9829 =
                                     let uu____9830 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9830.FStar_Syntax_Syntax.n in
                                   (match uu____9829 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9833::[],body,uu____9835) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9862 -> tm1)
                                    | uu____9865 -> tm1)
                               | uu____9866 -> tm1
                             else
                               (let uu____9876 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9876
                                then
                                  match args with
                                  | (t,uu____9878)::[] ->
                                      let uu____9895 =
                                        let uu____9896 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9896.FStar_Syntax_Syntax.n in
                                      (match uu____9895 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9899::[],body,uu____9901)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9928 -> tm1)
                                       | uu____9931 -> tm1)
                                  | (uu____9932,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9933))::(t,uu____9935)::[] ->
                                      let uu____9974 =
                                        let uu____9975 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9975.FStar_Syntax_Syntax.n in
                                      (match uu____9974 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9978::[],body,uu____9980)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10007 -> tm1)
                                       | uu____10010 -> tm1)
                                  | uu____10011 -> tm1
                                else
                                  (let uu____10021 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10021
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10022;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10023;_},uu____10024)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10041;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10042;_},uu____10043)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10060 -> tm1
                                   else reduce_equality cfg env stack tm1))))))
             | uu____10070 -> tm1)
let is_norm_request:
  'Auu____10074 .
    FStar_Syntax_Syntax.term -> 'Auu____10074 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10087 =
        let uu____10094 =
          let uu____10095 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10095.FStar_Syntax_Syntax.n in
        (uu____10094, args) in
      match uu____10087 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10101::uu____10102::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10106::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10111::uu____10112::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10115 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___196_10126  ->
    match uu___196_10126 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10132 =
          let uu____10135 =
            let uu____10136 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10136 in
          [uu____10135] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10132
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10151 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10151) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10189 =
          let uu____10192 =
            let uu____10197 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10197 s in
          FStar_All.pipe_right uu____10192 FStar_Util.must in
        FStar_All.pipe_right uu____10189 tr_norm_steps in
      match args with
      | uu____10222::(tm,uu____10224)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10247)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10262)::uu____10263::(tm,uu____10265)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10305 =
              let uu____10308 = full_norm steps in parse_steps uu____10308 in
            Beta :: uu____10305 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10317 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___197_10334  ->
    match uu___197_10334 with
    | (App
        (uu____10337,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10338;
                       FStar_Syntax_Syntax.vars = uu____10339;_},uu____10340,uu____10341))::uu____10342
        -> true
    | uu____10349 -> false
let firstn:
  'Auu____10355 .
    Prims.int ->
      'Auu____10355 Prims.list ->
        ('Auu____10355 Prims.list,'Auu____10355 Prims.list)
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
          (uu____10391,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10392;
                         FStar_Syntax_Syntax.vars = uu____10393;_},uu____10394,uu____10395))::uu____10396
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10403 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____10558  ->
               let uu____10559 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10560 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10561 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____10568 =
                 let uu____10569 =
                   let uu____10572 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10572 in
                 stack_to_string uu____10569 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10559 uu____10560 uu____10561 uu____10568);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10595 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10620 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10637 =
                 let uu____10638 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10639 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10638 uu____10639 in
               failwith uu____10637
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10640 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10657 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10658 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10659;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10660;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10663;
                 FStar_Syntax_Syntax.fv_delta = uu____10664;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10665;
                 FStar_Syntax_Syntax.fv_delta = uu____10666;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10667);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____10675 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____10675 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____10681  ->
                     let uu____10682 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10683 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____10682 uu____10683);
                if b
                then
                  (let uu____10684 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____10684 t1 fv)
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
                 let uu___232_10723 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___232_10723.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___232_10723.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10756 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10756) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___233_10764 = cfg in
                 let uu____10765 =
                   FStar_List.filter
                     (fun uu___198_10768  ->
                        match uu___198_10768 with
                        | UnfoldOnly uu____10769 -> false
                        | NoDeltaSteps  -> false
                        | uu____10772 -> true) cfg.steps in
                 {
                   steps = uu____10765;
                   tcenv = (uu___233_10764.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___233_10764.primitive_steps);
                   strong = (uu___233_10764.strong)
                 } in
               let uu____10773 = get_norm_request (norm cfg' env []) args in
               (match uu____10773 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10789 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___199_10794  ->
                                match uu___199_10794 with
                                | UnfoldUntil uu____10795 -> true
                                | UnfoldOnly uu____10796 -> true
                                | uu____10799 -> false)) in
                      if uu____10789
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___234_10804 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___234_10804.tcenv);
                        delta_level;
                        primitive_steps = (uu___234_10804.primitive_steps);
                        strong = (uu___234_10804.strong)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____10811 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10811
                      then
                        let uu____10814 =
                          let uu____10815 =
                            let uu____10820 = FStar_Util.now () in
                            (t1, uu____10820) in
                          Debug uu____10815 in
                        uu____10814 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____10824 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____10824
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____10831 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____10831
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10834 =
                      let uu____10841 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____10841, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____10834 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___200_10854  ->
                         match uu___200_10854 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____10857 =
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
                 if uu____10857
                 then false
                 else
                   (let uu____10859 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___201_10866  ->
                              match uu___201_10866 with
                              | UnfoldOnly uu____10867 -> true
                              | uu____10870 -> false)) in
                    match uu____10859 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____10874 -> should_delta) in
               (log cfg
                  (fun uu____10882  ->
                     let uu____10883 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____10884 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____10885 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____10883 uu____10884 uu____10885);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10888 = lookup_bvar env x in
               (match uu____10888 with
                | Univ uu____10891 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____10940 = FStar_ST.op_Bang r in
                      (match uu____10940 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11077  ->
                                 let uu____11078 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11079 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11078
                                   uu____11079);
                            (let uu____11080 =
                               let uu____11081 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11081.FStar_Syntax_Syntax.n in
                             match uu____11080 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11084 ->
                                 norm cfg env2 stack t'
                             | uu____11101 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11159)::uu____11160 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11169)::uu____11170 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11180,uu____11181))::stack_rest ->
                    (match c with
                     | Univ uu____11185 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11194 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11215  ->
                                    let uu____11216 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11216);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11256  ->
                                    let uu____11257 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11257);
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
                       (fun uu____11327  ->
                          let uu____11328 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11328);
                     norm cfg env stack1 t1)
                | (Debug uu____11329)::uu____11330 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11337 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11337
                    else
                      (let uu____11339 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11339 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11381  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11409 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11409
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11419 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11419)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_11424 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_11424.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_11424.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11425 -> lopt in
                           (log cfg
                              (fun uu____11431  ->
                                 let uu____11432 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11432);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___236_11441 = cfg in
                               {
                                 steps = (uu___236_11441.steps);
                                 tcenv = (uu___236_11441.tcenv);
                                 delta_level = (uu___236_11441.delta_level);
                                 primitive_steps =
                                   (uu___236_11441.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11452)::uu____11453 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11460 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11460
                    else
                      (let uu____11462 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11462 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11504  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11532 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11532
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11542 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11542)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_11547 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_11547.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_11547.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11548 -> lopt in
                           (log cfg
                              (fun uu____11554  ->
                                 let uu____11555 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11555);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___236_11564 = cfg in
                               {
                                 steps = (uu___236_11564.steps);
                                 tcenv = (uu___236_11564.tcenv);
                                 delta_level = (uu___236_11564.delta_level);
                                 primitive_steps =
                                   (uu___236_11564.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11575)::uu____11576 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11587 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11587
                    else
                      (let uu____11589 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11589 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11631  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11659 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11659
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11669 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11669)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_11674 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_11674.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_11674.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11675 -> lopt in
                           (log cfg
                              (fun uu____11681  ->
                                 let uu____11682 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11682);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___236_11691 = cfg in
                               {
                                 steps = (uu___236_11691.steps);
                                 tcenv = (uu___236_11691.tcenv);
                                 delta_level = (uu___236_11691.delta_level);
                                 primitive_steps =
                                   (uu___236_11691.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11702)::uu____11703 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11714 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11714
                    else
                      (let uu____11716 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11716 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11758  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11786 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11786
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11796 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11796)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_11801 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_11801.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_11801.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11802 -> lopt in
                           (log cfg
                              (fun uu____11808  ->
                                 let uu____11809 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11809);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___236_11818 = cfg in
                               {
                                 steps = (uu___236_11818.steps);
                                 tcenv = (uu___236_11818.tcenv);
                                 delta_level = (uu___236_11818.delta_level);
                                 primitive_steps =
                                   (uu___236_11818.primitive_steps);
                                 strong = true
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11829)::uu____11830 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11845 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11845
                    else
                      (let uu____11847 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11847 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11889  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11917 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11917
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11927 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11927)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_11932 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_11932.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_11932.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11933 -> lopt in
                           (log cfg
                              (fun uu____11939  ->
                                 let uu____11940 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11940);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___236_11949 = cfg in
                               {
                                 steps = (uu___236_11949.steps);
                                 tcenv = (uu___236_11949.tcenv);
                                 delta_level = (uu___236_11949.delta_level);
                                 primitive_steps =
                                   (uu___236_11949.primitive_steps);
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
                      let uu____11960 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11960
                    else
                      (let uu____11962 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11962 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12004  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12032 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12032
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12042 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12042)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___235_12047 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___235_12047.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___235_12047.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12048 -> lopt in
                           (log cfg
                              (fun uu____12054  ->
                                 let uu____12055 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12055);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___236_12064 = cfg in
                               {
                                 steps = (uu___236_12064.steps);
                                 tcenv = (uu___236_12064.tcenv);
                                 delta_level = (uu___236_12064.delta_level);
                                 primitive_steps =
                                   (uu___236_12064.primitive_steps);
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
                      (fun uu____12113  ->
                         fun stack1  ->
                           match uu____12113 with
                           | (a,aq) ->
                               let uu____12125 =
                                 let uu____12126 =
                                   let uu____12133 =
                                     let uu____12134 =
                                       let uu____12165 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12165, false) in
                                     Clos uu____12134 in
                                   (uu____12133, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12126 in
                               uu____12125 :: stack1) args) in
               (log cfg
                  (fun uu____12241  ->
                     let uu____12242 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12242);
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
                             ((let uu___237_12278 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___237_12278.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___237_12278.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12279 ->
                      let uu____12284 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12284)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12287 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12287 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12318 =
                          let uu____12319 =
                            let uu____12326 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___238_12328 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___238_12328.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___238_12328.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12326) in
                          FStar_Syntax_Syntax.Tm_refine uu____12319 in
                        mk uu____12318 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12347 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12347
               else
                 (let uu____12349 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12349 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12357 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12381  -> dummy :: env1) env) in
                        norm_comp cfg uu____12357 c1 in
                      let t2 =
                        let uu____12403 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12403 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12462)::uu____12463 ->
                    (log cfg
                       (fun uu____12474  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12475)::uu____12476 ->
                    (log cfg
                       (fun uu____12487  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12488,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12489;
                                   FStar_Syntax_Syntax.vars = uu____12490;_},uu____12491,uu____12492))::uu____12493
                    ->
                    (log cfg
                       (fun uu____12502  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12503)::uu____12504 ->
                    (log cfg
                       (fun uu____12515  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12516 ->
                    (log cfg
                       (fun uu____12519  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12523  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12540 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____12540
                         | FStar_Util.Inr c ->
                             let uu____12548 = norm_comp cfg env c in
                             FStar_Util.Inr uu____12548 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____12554 =
                         let uu____12555 =
                           let uu____12556 =
                             let uu____12583 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____12583, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____12556 in
                         mk uu____12555 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack uu____12554))))
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
                         let uu____12693 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____12693 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___239_12713 = cfg in
                               let uu____12714 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___239_12713.steps);
                                 tcenv = uu____12714;
                                 delta_level = (uu___239_12713.delta_level);
                                 primitive_steps =
                                   (uu___239_12713.primitive_steps);
                                 strong = (uu___239_12713.strong)
                               } in
                             let norm1 t2 =
                               let uu____12719 =
                                 let uu____12720 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____12720 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12719 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___240_12723 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___240_12723.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___240_12723.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____12724 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____12724
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12735,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12736;
                               FStar_Syntax_Syntax.lbunivs = uu____12737;
                               FStar_Syntax_Syntax.lbtyp = uu____12738;
                               FStar_Syntax_Syntax.lbeff = uu____12739;
                               FStar_Syntax_Syntax.lbdef = uu____12740;_}::uu____12741),uu____12742)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12778 =
                 (let uu____12781 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12781) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12783 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12783))) in
               if uu____12778
               then
                 let binder =
                   let uu____12785 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____12785 in
                 let env1 =
                   let uu____12795 =
                     let uu____12802 =
                       let uu____12803 =
                         let uu____12834 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12834,
                           false) in
                       Clos uu____12803 in
                     ((FStar_Pervasives_Native.Some binder), uu____12802) in
                   uu____12795 :: env in
                 (log cfg
                    (fun uu____12919  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____12921 =
                    let uu____12926 =
                      let uu____12927 =
                        let uu____12928 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12928
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12927] in
                    FStar_Syntax_Subst.open_term uu____12926 body in
                  match uu____12921 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____12937  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____12945 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____12945 in
                          FStar_Util.Inl
                            (let uu___241_12955 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___241_12955.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___241_12955.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____12958  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___242_12960 = lb in
                           let uu____12961 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___242_12960.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___242_12960.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____12961
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____12996  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___243_13019 = cfg in
                           {
                             steps = (uu___243_13019.steps);
                             tcenv = (uu___243_13019.tcenv);
                             delta_level = (uu___243_13019.delta_level);
                             primitive_steps =
                               (uu___243_13019.primitive_steps);
                             strong = true
                           } in
                         log cfg1
                           (fun uu____13022  ->
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
               let uu____13039 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13039 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13075 =
                               let uu___244_13076 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___244_13076.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___244_13076.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13075 in
                           let uu____13077 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13077 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13103 =
                                   FStar_List.map (fun uu____13119  -> dummy)
                                     lbs1 in
                                 let uu____13120 =
                                   let uu____13129 =
                                     FStar_List.map
                                       (fun uu____13149  -> dummy) xs1 in
                                   FStar_List.append uu____13129 env in
                                 FStar_List.append uu____13103 uu____13120 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13173 =
                                       let uu___245_13174 = rc in
                                       let uu____13175 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___245_13174.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13175;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___245_13174.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13173
                                 | uu____13182 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___246_13186 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___246_13186.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___246_13186.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13196 =
                        FStar_List.map (fun uu____13212  -> dummy) lbs2 in
                      FStar_List.append uu____13196 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13220 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13220 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___247_13236 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___247_13236.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___247_13236.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13263 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13263
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13282 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13358  ->
                        match uu____13358 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___248_13479 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___248_13479.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___248_13479.FStar_Syntax_Syntax.sort)
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
               (match uu____13282 with
                | (rec_env,memos,uu____13676) ->
                    let uu____13729 =
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
                             let uu____14260 =
                               let uu____14267 =
                                 let uu____14268 =
                                   let uu____14299 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14299, false) in
                                 Clos uu____14268 in
                               (FStar_Pervasives_Native.None, uu____14267) in
                             uu____14260 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14401  ->
                     let uu____14402 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14402);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14424 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14426::uu____14427 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14432) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14433 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14464 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14478 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14478
                              | uu____14489 -> m in
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
              let uu____14501 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14501 in
            let uu____14502 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14502 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14515  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14526  ->
                      let uu____14527 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14528 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14527
                        uu____14528);
                 (let t1 =
                    let uu____14530 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____14530
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
                    | (UnivArgs (us',uu____14540))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____14595 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____14598 ->
                        let uu____14601 =
                          let uu____14602 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14602 in
                        failwith uu____14601
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
                let uu____14623 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____14623
                then
                  let uu___249_14624 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___249_14624.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___249_14624.primitive_steps);
                    strong = (uu___249_14624.strong)
                  }
                else
                  (let uu___250_14626 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___250_14626.tcenv);
                     delta_level = (uu___250_14626.delta_level);
                     primitive_steps = (uu___250_14626.primitive_steps);
                     strong = (uu___250_14626.strong)
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
                  (fun uu____14655  ->
                     let uu____14656 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____14657 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14656
                       uu____14657);
                (let uu____14658 =
                   let uu____14659 = FStar_Syntax_Subst.compress head2 in
                   uu____14659.FStar_Syntax_Syntax.n in
                 match uu____14658 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____14677 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____14677 with
                      | (uu____14678,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14684 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14692 =
                                   let uu____14693 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____14693.FStar_Syntax_Syntax.n in
                                 match uu____14692 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____14699,uu____14700))
                                     ->
                                     let uu____14709 =
                                       let uu____14710 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____14710.FStar_Syntax_Syntax.n in
                                     (match uu____14709 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14716,msrc,uu____14718))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14727 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____14727
                                      | uu____14728 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14729 ->
                                     FStar_Pervasives_Native.None in
                               let uu____14730 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____14730 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___251_14735 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___251_14735.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___251_14735.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___251_14735.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____14736 = FStar_List.tl stack in
                                    let uu____14737 =
                                      let uu____14738 =
                                        let uu____14741 =
                                          let uu____14742 =
                                            let uu____14755 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____14755) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14742 in
                                        FStar_Syntax_Syntax.mk uu____14741 in
                                      uu____14738
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____14736 uu____14737
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14771 =
                                      let uu____14772 = is_return body in
                                      match uu____14772 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14776;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14777;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14782 -> false in
                                    if uu____14771
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let head3 =
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
                                         let uu____14804 =
                                           let uu____14807 =
                                             let uu____14808 =
                                               let uu____14825 =
                                                 let uu____14828 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____14828] in
                                               (uu____14825, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14808 in
                                           FStar_Syntax_Syntax.mk uu____14807 in
                                         uu____14804
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____14844 =
                                           let uu____14845 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____14845.FStar_Syntax_Syntax.n in
                                         match uu____14844 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14851::uu____14852::[])
                                             ->
                                             let uu____14859 =
                                               let uu____14862 =
                                                 let uu____14863 =
                                                   let uu____14870 =
                                                     let uu____14873 =
                                                       let uu____14874 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14874 in
                                                     let uu____14875 =
                                                       let uu____14878 =
                                                         let uu____14879 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14879 in
                                                       [uu____14878] in
                                                     uu____14873 ::
                                                       uu____14875 in
                                                   (bind1, uu____14870) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14863 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14862 in
                                             uu____14859
                                               FStar_Pervasives_Native.None
                                               head3.FStar_Syntax_Syntax.pos
                                         | uu____14887 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____14893 =
                                           let uu____14896 =
                                             let uu____14897 =
                                               let uu____14912 =
                                                 let uu____14915 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____14916 =
                                                   let uu____14919 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____14920 =
                                                     let uu____14923 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____14924 =
                                                       let uu____14927 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____14928 =
                                                         let uu____14931 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____14932 =
                                                           let uu____14935 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____14935] in
                                                         uu____14931 ::
                                                           uu____14932 in
                                                       uu____14927 ::
                                                         uu____14928 in
                                                     uu____14923 ::
                                                       uu____14924 in
                                                   uu____14919 :: uu____14920 in
                                                 uu____14915 :: uu____14916 in
                                               (bind_inst, uu____14912) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14897 in
                                           FStar_Syntax_Syntax.mk uu____14896 in
                                         uu____14893
                                           FStar_Pervasives_Native.None
                                           head3.FStar_Syntax_Syntax.pos in
                                       let uu____14943 = FStar_List.tl stack in
                                       norm cfg env uu____14943 reified))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____14967 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____14967 with
                      | (uu____14968,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15003 =
                                  let uu____15004 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15004.FStar_Syntax_Syntax.n in
                                match uu____15003 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15010) -> t2
                                | uu____15015 -> head3 in
                              let uu____15016 =
                                let uu____15017 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15017.FStar_Syntax_Syntax.n in
                              match uu____15016 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15023 -> FStar_Pervasives_Native.None in
                            let uu____15024 = maybe_extract_fv head3 in
                            match uu____15024 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15034 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15034
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15039 = maybe_extract_fv head4 in
                                  match uu____15039 with
                                  | FStar_Pervasives_Native.Some uu____15044
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15045 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15050 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15065 =
                              match uu____15065 with
                              | (e,q) ->
                                  let uu____15072 =
                                    let uu____15073 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15073.FStar_Syntax_Syntax.n in
                                  (match uu____15072 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15088 -> false) in
                            let uu____15089 =
                              let uu____15090 =
                                let uu____15097 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15097 :: args in
                              FStar_Util.for_some is_arg_impure uu____15090 in
                            if uu____15089
                            then
                              let uu____15102 =
                                let uu____15103 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15103 in
                              failwith uu____15102
                            else ());
                           (let uu____15105 = maybe_unfold_action head_app in
                            match uu____15105 with
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
                                let uu____15142 = FStar_List.tl stack in
                                norm cfg env uu____15142 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15144) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15168 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15168 in
                     let uu____15169 = FStar_List.tl stack in
                     norm cfg env uu____15169 lifted
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15290  ->
                               match uu____15290 with
                               | (pat,wopt,tm) ->
                                   let uu____15338 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15338))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____15370 = FStar_List.tl stack in
                     norm cfg env uu____15370 tm
                 | uu____15371 -> fallback ())
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
              (fun uu____15383  ->
                 let uu____15384 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print1 "Reifying lift: %s\n" uu____15384);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____15386 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15386 with
               | (uu____15387,return_repr) ->
                   let return_inst =
                     let uu____15396 =
                       let uu____15397 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15397.FStar_Syntax_Syntax.n in
                     match uu____15396 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15403::[]) ->
                         let uu____15410 =
                           let uu____15413 =
                             let uu____15414 =
                               let uu____15421 =
                                 let uu____15424 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15424] in
                               (return_tm, uu____15421) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15414 in
                           FStar_Syntax_Syntax.mk uu____15413 in
                         uu____15410 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15432 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15435 =
                     let uu____15438 =
                       let uu____15439 =
                         let uu____15454 =
                           let uu____15457 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15458 =
                             let uu____15461 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15461] in
                           uu____15457 :: uu____15458 in
                         (return_inst, uu____15454) in
                       FStar_Syntax_Syntax.Tm_app uu____15439 in
                     FStar_Syntax_Syntax.mk uu____15438 in
                   uu____15435 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15470 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15470 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15473 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15473
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15474;
                     FStar_TypeChecker_Env.mtarget = uu____15475;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15476;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15487;
                     FStar_TypeChecker_Env.mtarget = uu____15488;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15489;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15507 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____15507)
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
                (fun uu____15563  ->
                   match uu____15563 with
                   | (a,imp) ->
                       let uu____15574 = norm cfg env [] a in
                       (uu____15574, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___252_15591 = comp1 in
            let uu____15594 =
              let uu____15595 =
                let uu____15604 = norm cfg env [] t in
                let uu____15605 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15604, uu____15605) in
              FStar_Syntax_Syntax.Total uu____15595 in
            {
              FStar_Syntax_Syntax.n = uu____15594;
              FStar_Syntax_Syntax.pos =
                (uu___252_15591.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___252_15591.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___253_15620 = comp1 in
            let uu____15623 =
              let uu____15624 =
                let uu____15633 = norm cfg env [] t in
                let uu____15634 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15633, uu____15634) in
              FStar_Syntax_Syntax.GTotal uu____15624 in
            {
              FStar_Syntax_Syntax.n = uu____15623;
              FStar_Syntax_Syntax.pos =
                (uu___253_15620.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___253_15620.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15686  ->
                      match uu____15686 with
                      | (a,i) ->
                          let uu____15697 = norm cfg env [] a in
                          (uu____15697, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___202_15708  ->
                      match uu___202_15708 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15712 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15712
                      | f -> f)) in
            let uu___254_15716 = comp1 in
            let uu____15719 =
              let uu____15720 =
                let uu___255_15721 = ct in
                let uu____15722 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15723 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15726 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15722;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___255_15721.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15723;
                  FStar_Syntax_Syntax.effect_args = uu____15726;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15720 in
            {
              FStar_Syntax_Syntax.n = uu____15719;
              FStar_Syntax_Syntax.pos =
                (uu___254_15716.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___254_15716.FStar_Syntax_Syntax.vars)
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
            (let uu___256_15744 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___256_15744.tcenv);
               delta_level = (uu___256_15744.delta_level);
               primitive_steps = (uu___256_15744.primitive_steps);
               strong = (uu___256_15744.strong)
             }) env [] t in
        let non_info t =
          let uu____15749 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15749 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15752 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___257_15771 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___257_15771.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___257_15771.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15778 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15778
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
                    let uu___258_15789 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___258_15789.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___258_15789.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___258_15789.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___259_15791 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___259_15791.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___259_15791.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___259_15791.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___259_15791.FStar_Syntax_Syntax.flags)
                    } in
              let uu___260_15792 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___260_15792.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___260_15792.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15794 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15797  ->
        match uu____15797 with
        | (x,imp) ->
            let uu____15800 =
              let uu___261_15801 = x in
              let uu____15802 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___261_15801.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___261_15801.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15802
              } in
            (uu____15800, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15808 =
          FStar_List.fold_left
            (fun uu____15826  ->
               fun b  ->
                 match uu____15826 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____15808 with | (nbs,uu____15866) -> FStar_List.rev nbs
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
            let uu____15882 =
              let uu___262_15883 = rc in
              let uu____15884 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___262_15883.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15884;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___262_15883.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15882
        | uu____15891 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____15904  ->
               let uu____15905 = FStar_Syntax_Print.tag_of_term t in
               let uu____15906 = FStar_Syntax_Print.term_to_string t in
               let uu____15907 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____15914 =
                 let uu____15915 =
                   let uu____15918 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____15918 in
                 stack_to_string uu____15915 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____15905 uu____15906 uu____15907 uu____15914);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____15947 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____15947
                 then
                   let time_now = FStar_Util.now () in
                   let uu____15949 =
                     let uu____15950 =
                       let uu____15951 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____15951 in
                     FStar_Util.string_of_int uu____15950 in
                   let uu____15956 = FStar_Syntax_Print.term_to_string tm in
                   let uu____15957 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____15949 uu____15956 uu____15957
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16003  ->
                     let uu____16004 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16004);
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
               let uu____16040 =
                 let uu___263_16041 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___263_16041.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___263_16041.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16040
           | (Arg (Univ uu____16042,uu____16043,uu____16044))::uu____16045 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16048,uu____16049))::uu____16050 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16066),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16119  ->
                     let uu____16120 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16120);
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
                  (let uu____16130 = FStar_ST.op_Bang m in
                   match uu____16130 with
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
                   | FStar_Pervasives_Native.Some (uu____16274,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback uu____16318 =
                 log cfg
                   (fun uu____16322  ->
                      let uu____16323 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print1 "Not reifying: %s\n" uu____16323);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  let uu____16327 = maybe_simplify cfg env1 stack' t1 in
                  rebuild cfg env1 stack' uu____16327) in
               let uu____16330 =
                 let uu____16331 = FStar_Syntax_Subst.compress t in
                 uu____16331.FStar_Syntax_Syntax.n in
               (match uu____16330 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic fallback cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (m,m',ty)) ->
                    let uu____16357 =
                      let uu____16358 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 m m' uu____16358 in
                    norm cfg env1 stack uu____16357
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16359);
                       FStar_Syntax_Syntax.pos = uu____16360;
                       FStar_Syntax_Syntax.vars = uu____16361;_},(e,uu____16363)::[])
                    -> norm cfg env1 stack' e
                | uu____16392 -> fallback ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16403 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16403
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16415  ->
                     let uu____16416 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16416);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16421 =
                   log cfg
                     (fun uu____16426  ->
                        let uu____16427 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16428 =
                          let uu____16429 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16446  ->
                                    match uu____16446 with
                                    | (p,uu____16456,uu____16457) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16429
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16427 uu____16428);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___203_16474  ->
                                match uu___203_16474 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16475 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___264_16479 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___264_16479.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___264_16479.primitive_steps);
                        strong = true
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16511 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16532 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16592  ->
                                    fun uu____16593  ->
                                      match (uu____16592, uu____16593) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____16684 = norm_pat env3 p1 in
                                          (match uu____16684 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16532 with
                           | (pats1,env3) ->
                               ((let uu___265_16766 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___265_16766.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___266_16785 = x in
                            let uu____16786 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___266_16785.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___266_16785.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____16786
                            } in
                          ((let uu___267_16800 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___267_16800.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___268_16811 = x in
                            let uu____16812 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___268_16811.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___268_16811.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____16812
                            } in
                          ((let uu___269_16826 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___269_16826.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___270_16842 = x in
                            let uu____16843 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___270_16842.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___270_16842.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____16843
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___271_16850 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___271_16850.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____16860 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____16874 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____16874 with
                                  | (p,wopt,e) ->
                                      let uu____16894 = norm_pat env1 p in
                                      (match uu____16894 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____16919 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____16919 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____16925 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____16925) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____16935) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____16940 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____16941;
                         FStar_Syntax_Syntax.fv_delta = uu____16942;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____16943;
                         FStar_Syntax_Syntax.fv_delta = uu____16944;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____16945);_}
                       -> true
                   | uu____16952 -> false in
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
                   let uu____17097 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17097 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17184 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17223 ->
                                 let uu____17224 =
                                   let uu____17225 = is_cons head1 in
                                   Prims.op_Negation uu____17225 in
                                 FStar_Util.Inr uu____17224)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17250 =
                              let uu____17251 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17251.FStar_Syntax_Syntax.n in
                            (match uu____17250 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17269 ->
                                 let uu____17270 =
                                   let uu____17271 = is_cons head1 in
                                   Prims.op_Negation uu____17271 in
                                 FStar_Util.Inr uu____17270))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17340)::rest_a,(p1,uu____17343)::rest_p) ->
                       let uu____17387 = matches_pat t1 p1 in
                       (match uu____17387 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17436 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17542 = matches_pat scrutinee1 p1 in
                       (match uu____17542 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17582  ->
                                  let uu____17583 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17584 =
                                    let uu____17585 =
                                      FStar_List.map
                                        (fun uu____17595  ->
                                           match uu____17595 with
                                           | (uu____17600,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17585
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17583 uu____17584);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____17631  ->
                                       match uu____17631 with
                                       | (bv,t1) ->
                                           let uu____17654 =
                                             let uu____17661 =
                                               let uu____17664 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____17664 in
                                             let uu____17665 =
                                               let uu____17666 =
                                                 let uu____17697 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____17697, false) in
                                               Clos uu____17666 in
                                             (uu____17661, uu____17665) in
                                           uu____17654 :: env2) env1 s in
                              let uu____17806 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____17806))) in
                 let uu____17807 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____17807
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___204_17828  ->
                match uu___204_17828 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____17832 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____17838 -> d in
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
            let uu___272_17863 = config s e in
            {
              steps = (uu___272_17863.steps);
              tcenv = (uu___272_17863.tcenv);
              delta_level = (uu___272_17863.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___272_17863.strong)
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
      fun t  -> let uu____17888 = config s e in norm_comp uu____17888 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____17901 = config [] env in norm_universe uu____17901 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____17914 = config [] env in ghost_to_pure_aux uu____17914 [] c
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
        let uu____17932 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____17932 in
      let uu____17939 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____17939
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___273_17941 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___273_17941.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___273_17941.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____17944  ->
                    let uu____17945 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____17945))
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
            ((let uu____17962 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____17962);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____17973 = config [AllowUnboundUniverses] env in
          norm_comp uu____17973 [] c
        with
        | e ->
            ((let uu____17986 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____17986);
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
                   let uu____18023 =
                     let uu____18024 =
                       let uu____18031 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18031) in
                     FStar_Syntax_Syntax.Tm_refine uu____18024 in
                   mk uu____18023 t01.FStar_Syntax_Syntax.pos
               | uu____18036 -> t2)
          | uu____18037 -> t2 in
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
        let uu____18077 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18077 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18106 ->
                 let uu____18113 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18113 with
                  | (actuals,uu____18123,uu____18124) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18138 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18138 with
                         | (binders,args) ->
                             let uu____18155 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18155
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
      | uu____18163 ->
          let uu____18164 = FStar_Syntax_Util.head_and_args t in
          (match uu____18164 with
           | (head1,args) ->
               let uu____18201 =
                 let uu____18202 = FStar_Syntax_Subst.compress head1 in
                 uu____18202.FStar_Syntax_Syntax.n in
               (match uu____18201 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18205,thead) ->
                    let uu____18231 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18231 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18273 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___278_18281 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___278_18281.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___278_18281.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___278_18281.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___278_18281.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___278_18281.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___278_18281.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___278_18281.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___278_18281.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___278_18281.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___278_18281.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___278_18281.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___278_18281.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___278_18281.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___278_18281.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___278_18281.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___278_18281.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___278_18281.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___278_18281.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___278_18281.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___278_18281.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___278_18281.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___278_18281.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___278_18281.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___278_18281.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___278_18281.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___278_18281.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___278_18281.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___278_18281.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___278_18281.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___278_18281.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___278_18281.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18273 with
                            | (uu____18282,ty,uu____18284) ->
                                eta_expand_with_type env t ty))
                | uu____18285 ->
                    let uu____18286 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___279_18294 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___279_18294.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___279_18294.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___279_18294.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___279_18294.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___279_18294.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___279_18294.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___279_18294.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___279_18294.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___279_18294.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___279_18294.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___279_18294.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___279_18294.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___279_18294.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___279_18294.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___279_18294.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___279_18294.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___279_18294.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___279_18294.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___279_18294.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___279_18294.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___279_18294.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___279_18294.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___279_18294.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___279_18294.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___279_18294.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___279_18294.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___279_18294.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___279_18294.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___279_18294.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___279_18294.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___279_18294.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18286 with
                     | (uu____18295,ty,uu____18297) ->
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
            | (uu____18371,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18377,FStar_Util.Inl t) ->
                let uu____18383 =
                  let uu____18386 =
                    let uu____18387 =
                      let uu____18400 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____18400) in
                    FStar_Syntax_Syntax.Tm_arrow uu____18387 in
                  FStar_Syntax_Syntax.mk uu____18386 in
                uu____18383 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____18404 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____18404 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____18431 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18486 ->
                    let uu____18487 =
                      let uu____18496 =
                        let uu____18497 = FStar_Syntax_Subst.compress t3 in
                        uu____18497.FStar_Syntax_Syntax.n in
                      (uu____18496, tc) in
                    (match uu____18487 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18522) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____18559) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____18598,FStar_Util.Inl uu____18599) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____18622 -> failwith "Impossible") in
              (match uu____18431 with
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
          let uu____18727 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____18727 with
          | (univ_names1,binders1,tc) ->
              let uu____18785 = FStar_Util.left tc in
              (univ_names1, binders1, uu____18785)
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
          let uu____18820 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____18820 with
          | (univ_names1,binders1,tc) ->
              let uu____18880 = FStar_Util.right tc in
              (univ_names1, binders1, uu____18880)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____18913 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____18913 with
           | (univ_names1,binders1,typ1) ->
               let uu___280_18941 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___280_18941.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___280_18941.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___280_18941.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___280_18941.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___281_18962 = s in
          let uu____18963 =
            let uu____18964 =
              let uu____18973 = FStar_List.map (elim_uvars env) sigs in
              (uu____18973, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18964 in
          {
            FStar_Syntax_Syntax.sigel = uu____18963;
            FStar_Syntax_Syntax.sigrng =
              (uu___281_18962.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___281_18962.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___281_18962.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___281_18962.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18990 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18990 with
           | (univ_names1,uu____19008,typ1) ->
               let uu___282_19022 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___282_19022.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___282_19022.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___282_19022.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___282_19022.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19028 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19028 with
           | (univ_names1,uu____19046,typ1) ->
               let uu___283_19060 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___283_19060.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___283_19060.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___283_19060.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___283_19060.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19094 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19094 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19117 =
                            let uu____19118 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19118 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19117 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___284_19121 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___284_19121.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___284_19121.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___285_19122 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___285_19122.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___285_19122.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___285_19122.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___285_19122.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___286_19134 = s in
          let uu____19135 =
            let uu____19136 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19136 in
          {
            FStar_Syntax_Syntax.sigel = uu____19135;
            FStar_Syntax_Syntax.sigrng =
              (uu___286_19134.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___286_19134.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___286_19134.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___286_19134.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19140 = elim_uvars_aux_t env us [] t in
          (match uu____19140 with
           | (us1,uu____19158,t1) ->
               let uu___287_19172 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___287_19172.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___287_19172.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___287_19172.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___287_19172.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19173 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19175 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19175 with
           | (univs1,binders,signature) ->
               let uu____19203 =
                 let uu____19212 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19212 with
                 | (univs_opening,univs2) ->
                     let uu____19239 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19239) in
               (match uu____19203 with
                | (univs_opening,univs_closing) ->
                    let uu____19256 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19262 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19263 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19262, uu____19263) in
                    (match uu____19256 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19285 =
                           match uu____19285 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19303 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19303 with
                                | (us1,t1) ->
                                    let uu____19314 =
                                      let uu____19319 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19326 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19319, uu____19326) in
                                    (match uu____19314 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19339 =
                                           let uu____19344 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____19353 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____19344, uu____19353) in
                                         (match uu____19339 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19369 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19369 in
                                              let uu____19370 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____19370 with
                                               | (uu____19391,uu____19392,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19407 =
                                                       let uu____19408 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19408 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19407 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____19413 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____19413 with
                           | (uu____19426,uu____19427,t1) -> t1 in
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
                             | uu____19487 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____19504 =
                               let uu____19505 =
                                 FStar_Syntax_Subst.compress body in
                               uu____19505.FStar_Syntax_Syntax.n in
                             match uu____19504 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____19564 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____19593 =
                               let uu____19594 =
                                 FStar_Syntax_Subst.compress t in
                               uu____19594.FStar_Syntax_Syntax.n in
                             match uu____19593 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____19615) ->
                                 let uu____19636 = destruct_action_body body in
                                 (match uu____19636 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____19681 ->
                                 let uu____19682 = destruct_action_body t in
                                 (match uu____19682 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____19731 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____19731 with
                           | (action_univs,t) ->
                               let uu____19740 = destruct_action_typ_templ t in
                               (match uu____19740 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___288_19781 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___288_19781.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___288_19781.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___289_19783 = ed in
                           let uu____19784 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____19785 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____19786 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____19787 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____19788 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____19789 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____19790 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____19791 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____19792 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____19793 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____19794 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____19795 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____19796 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____19797 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___289_19783.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___289_19783.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____19784;
                             FStar_Syntax_Syntax.bind_wp = uu____19785;
                             FStar_Syntax_Syntax.if_then_else = uu____19786;
                             FStar_Syntax_Syntax.ite_wp = uu____19787;
                             FStar_Syntax_Syntax.stronger = uu____19788;
                             FStar_Syntax_Syntax.close_wp = uu____19789;
                             FStar_Syntax_Syntax.assert_p = uu____19790;
                             FStar_Syntax_Syntax.assume_p = uu____19791;
                             FStar_Syntax_Syntax.null_wp = uu____19792;
                             FStar_Syntax_Syntax.trivial = uu____19793;
                             FStar_Syntax_Syntax.repr = uu____19794;
                             FStar_Syntax_Syntax.return_repr = uu____19795;
                             FStar_Syntax_Syntax.bind_repr = uu____19796;
                             FStar_Syntax_Syntax.actions = uu____19797
                           } in
                         let uu___290_19800 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___290_19800.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___290_19800.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___290_19800.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___290_19800.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___205_19817 =
            match uu___205_19817 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____19844 = elim_uvars_aux_t env us [] t in
                (match uu____19844 with
                 | (us1,uu____19868,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___291_19887 = sub_eff in
            let uu____19888 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____19891 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___291_19887.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___291_19887.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____19888;
              FStar_Syntax_Syntax.lift = uu____19891
            } in
          let uu___292_19894 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___292_19894.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___292_19894.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___292_19894.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___292_19894.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____19904 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____19904 with
           | (univ_names1,binders1,comp1) ->
               let uu___293_19938 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___293_19938.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___293_19938.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___293_19938.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___293_19938.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____19949 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t