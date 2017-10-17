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
let set_memo:
  'Auu____1425 'Auu____1426 .
    ('Auu____1426 FStar_Pervasives_Native.option,'Auu____1425) FStar_ST.mref
      -> 'Auu____1426 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1721 = FStar_ST.op_Bang r in
      match uu____1721 with
      | FStar_Pervasives_Native.Some uu____1822 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1929 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1929 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___179_1937  ->
    match uu___179_1937 with
    | Arg (c,uu____1939,uu____1940) ->
        let uu____1941 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1941
    | MemoLazy uu____1942 -> "MemoLazy"
    | Abs (uu____1949,bs,uu____1951,uu____1952,uu____1953) ->
        let uu____1958 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1958
    | UnivArgs uu____1963 -> "UnivArgs"
    | Match uu____1970 -> "Match"
    | App (uu____1977,t,uu____1979,uu____1980) ->
        let uu____1981 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1981
    | Meta (m,uu____1983) -> "Meta"
    | Let uu____1984 -> "Let"
    | Steps (uu____1993,uu____1994,uu____1995) -> "Steps"
    | Debug (t,uu____2005) ->
        let uu____2006 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____2006
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____2015 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____2015 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____2033 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____2033 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____2048 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____2048 then f () else ()
let is_empty: 'Auu____2054 . 'Auu____2054 Prims.list -> Prims.bool =
  fun uu___180_2060  ->
    match uu___180_2060 with | [] -> true | uu____2063 -> false
let lookup_bvar:
  'Auu____2074 'Auu____2075 .
    ('Auu____2075,'Auu____2074) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2074
  =
  fun env  ->
    fun x  ->
      try
        let uu____2099 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____2099
      with
      | uu____2112 ->
          let uu____2113 =
            let uu____2114 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____2114 in
          failwith uu____2113
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
          let uu____2155 =
            FStar_List.fold_left
              (fun uu____2181  ->
                 fun u1  ->
                   match uu____2181 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2206 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____2206 with
                        | (k_u,n1) ->
                            let uu____2221 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2221
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____2155 with
          | (uu____2239,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2264 =
                   let uu____2265 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____2265 in
                 match uu____2264 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2283 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2292 ->
                   let uu____2293 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2293
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2299 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2308 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2317 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2324 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2324 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2341 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2341 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2349 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2357 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2357 with
                                  | (uu____2362,m) -> n1 <= m)) in
                        if uu____2349 then rest1 else us1
                    | uu____2367 -> us1)
               | uu____2372 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2376 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2376 in
        let uu____2379 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2379
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2381 = aux u in
           match uu____2381 with
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
          (fun uu____2485  ->
             let uu____2486 = FStar_Syntax_Print.tag_of_term t in
             let uu____2487 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2486
               uu____2487);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2494 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2496 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2521 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2522 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2523 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2524 ->
                  let uu____2541 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2541
                  then
                    let uu____2542 =
                      let uu____2543 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2544 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2543 uu____2544 in
                    failwith uu____2542
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2547 =
                    let uu____2548 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2548 in
                  mk uu____2547 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2555 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2555
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2557 = lookup_bvar env x in
                  (match uu____2557 with
                   | Univ uu____2560 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2564) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2676 = closures_as_binders_delayed cfg env bs in
                  (match uu____2676 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2704 =
                         let uu____2705 =
                           let uu____2722 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2722) in
                         FStar_Syntax_Syntax.Tm_abs uu____2705 in
                       mk uu____2704 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2753 = closures_as_binders_delayed cfg env bs in
                  (match uu____2753 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2795 =
                    let uu____2806 =
                      let uu____2813 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2813] in
                    closures_as_binders_delayed cfg env uu____2806 in
                  (match uu____2795 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2831 =
                         let uu____2832 =
                           let uu____2839 =
                             let uu____2840 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2840
                               FStar_Pervasives_Native.fst in
                           (uu____2839, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2832 in
                       mk uu____2831 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2931 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2931
                    | FStar_Util.Inr c ->
                        let uu____2945 = close_comp cfg env c in
                        FStar_Util.Inr uu____2945 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2961 =
                    let uu____2962 =
                      let uu____2989 = closure_as_term_delayed cfg env t11 in
                      (uu____2989, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2962 in
                  mk uu____2961 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3040 =
                    let uu____3041 =
                      let uu____3048 = closure_as_term_delayed cfg env t' in
                      let uu____3051 =
                        let uu____3052 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____3052 in
                      (uu____3048, uu____3051) in
                    FStar_Syntax_Syntax.Tm_meta uu____3041 in
                  mk uu____3040 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3112 =
                    let uu____3113 =
                      let uu____3120 = closure_as_term_delayed cfg env t' in
                      let uu____3123 =
                        let uu____3124 =
                          let uu____3131 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____3131) in
                        FStar_Syntax_Syntax.Meta_monadic uu____3124 in
                      (uu____3120, uu____3123) in
                    FStar_Syntax_Syntax.Tm_meta uu____3113 in
                  mk uu____3112 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3150 =
                    let uu____3151 =
                      let uu____3158 = closure_as_term_delayed cfg env t' in
                      let uu____3161 =
                        let uu____3162 =
                          let uu____3171 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____3171) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3162 in
                      (uu____3158, uu____3161) in
                    FStar_Syntax_Syntax.Tm_meta uu____3151 in
                  mk uu____3150 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3184 =
                    let uu____3185 =
                      let uu____3192 = closure_as_term_delayed cfg env t' in
                      (uu____3192, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____3185 in
                  mk uu____3184 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3232  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3251 =
                    let uu____3262 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3262
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3281 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___200_3293 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___200_3293.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___200_3293.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3281)) in
                  (match uu____3251 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___201_3309 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___201_3309.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___201_3309.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3320,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3379  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3404 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3404
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3424  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3446 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3446
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___202_3458 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___202_3458.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___202_3458.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___203_3459 = lb in
                    let uu____3460 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___203_3459.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___203_3459.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3460
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3490  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3579 =
                    match uu____3579 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3634 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3655 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3715  ->
                                        fun uu____3716  ->
                                          match (uu____3715, uu____3716) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3807 =
                                                norm_pat env3 p1 in
                                              (match uu____3807 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3655 with
                               | (pats1,env3) ->
                                   ((let uu___204_3889 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___204_3889.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___205_3908 = x in
                                let uu____3909 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___205_3908.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___205_3908.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3909
                                } in
                              ((let uu___206_3923 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___206_3923.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___207_3934 = x in
                                let uu____3935 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___207_3934.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___207_3934.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3935
                                } in
                              ((let uu___208_3949 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___208_3949.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___209_3965 = x in
                                let uu____3966 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___209_3965.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___209_3965.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3966
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___210_3973 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___210_3973.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3976 = norm_pat env1 pat in
                        (match uu____3976 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4005 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____4005 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____4011 =
                    let uu____4012 =
                      let uu____4035 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____4035) in
                    FStar_Syntax_Syntax.Tm_match uu____4012 in
                  mk uu____4011 t1.FStar_Syntax_Syntax.pos))
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
        | uu____4121 -> closure_as_term cfg env t
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
        | uu____4147 ->
            FStar_List.map
              (fun uu____4164  ->
                 match uu____4164 with
                 | (x,imp) ->
                     let uu____4183 = closure_as_term_delayed cfg env x in
                     (uu____4183, imp)) args
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
        let uu____4197 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4246  ->
                  fun uu____4247  ->
                    match (uu____4246, uu____4247) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___211_4317 = b in
                          let uu____4318 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___211_4317.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___211_4317.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4318
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____4197 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4411 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4424 = closure_as_term_delayed cfg env t in
                 let uu____4425 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4424 uu____4425
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4438 = closure_as_term_delayed cfg env t in
                 let uu____4439 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4438 uu____4439
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
                        (fun uu___181_4465  ->
                           match uu___181_4465 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4469 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4469
                           | f -> f)) in
                 let uu____4473 =
                   let uu___212_4474 = c1 in
                   let uu____4475 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4475;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___212_4474.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4473)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___182_4485  ->
            match uu___182_4485 with
            | FStar_Syntax_Syntax.DECREASES uu____4486 -> false
            | uu____4489 -> true))
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
                   (fun uu___183_4507  ->
                      match uu___183_4507 with
                      | FStar_Syntax_Syntax.DECREASES uu____4508 -> false
                      | uu____4511 -> true)) in
            let rc1 =
              let uu___213_4513 = rc in
              let uu____4514 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___213_4513.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4514;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4521 -> lopt
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
    let uu____4609 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4609 in
  let arg_as_bounded_int uu____4637 =
    match uu____4637 with
    | (a,uu____4649) ->
        let uu____4656 =
          let uu____4657 = FStar_Syntax_Subst.compress a in
          uu____4657.FStar_Syntax_Syntax.n in
        (match uu____4656 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4667;
                FStar_Syntax_Syntax.vars = uu____4668;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4670;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4671;_},uu____4672)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4711 =
               let uu____4716 = FStar_Util.int_of_string i in
               (fv1, uu____4716) in
             FStar_Pervasives_Native.Some uu____4711
         | uu____4721 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4763 = f a in FStar_Pervasives_Native.Some uu____4763
    | uu____4764 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4814 = f a0 a1 in FStar_Pervasives_Native.Some uu____4814
    | uu____4815 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4864 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4864 in
  let binary_op as_a f res args =
    let uu____4920 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4920 in
  let as_primitive_step uu____4944 =
    match uu____4944 with
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
           let uu____4992 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4992) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5020 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____5020) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____5041 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____5041) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5069 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____5069) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5097 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____5097) in
  let list_of_string' rng s =
    let name l =
      let uu____5111 =
        let uu____5112 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5112 in
      mk uu____5111 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5122 =
      let uu____5125 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5125 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5122 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    FStar_Syntax_Embeddings.embed_int rng r in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5172 = arg_as_string a1 in
        (match uu____5172 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5178 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____5178 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5191 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____5191
              | uu____5192 -> FStar_Pervasives_Native.None)
         | uu____5197 -> FStar_Pervasives_Native.None)
    | uu____5200 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5210 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____5210 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5226 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____5226 in
  let string_of_bool2 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5256 args =
    match args with
    | uu____5268::(t,uu____5270)::[] ->
        let uu____5299 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5299
    | uu____5304 -> FStar_Pervasives_Native.None in
  let set_range_of1 uu____5326 args =
    match args with
    | uu____5336::(t,uu____5338)::(r,uu____5340)::[] ->
        let uu____5361 = FStar_Syntax_Embeddings.unembed_range_safe r in
        FStar_Util.bind_opt uu____5361
          (fun r1  ->
             FStar_Pervasives_Native.Some
               (let uu___214_5371 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_5371.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_5371.FStar_Syntax_Syntax.vars)
                }))
    | uu____5372 -> FStar_Pervasives_Native.None in
  let mk_range1 uu____5388 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5399 =
          let uu____5420 = arg_as_string fn in
          let uu____5423 = arg_as_int from_line in
          let uu____5426 = arg_as_int from_col in
          let uu____5429 = arg_as_int to_line in
          let uu____5432 = arg_as_int to_col in
          (uu____5420, uu____5423, uu____5426, uu____5429, uu____5432) in
        (match uu____5399 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5463 = FStar_Range.mk_pos from_l from_c in
               let uu____5464 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5463 uu____5464 in
             let uu____5465 = term_of_range r in
             FStar_Pervasives_Native.Some uu____5465
         | uu____5470 -> FStar_Pervasives_Native.None)
    | uu____5491 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5518)::(a1,uu____5520)::(a2,uu____5522)::[] ->
        let uu____5559 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5559 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5572 -> FStar_Pervasives_Native.None)
    | uu____5573 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5591 =
      let uu____5606 =
        let uu____5621 =
          let uu____5636 =
            let uu____5651 =
              let uu____5666 =
                let uu____5681 =
                  let uu____5696 =
                    let uu____5711 =
                      let uu____5726 =
                        let uu____5741 =
                          let uu____5756 =
                            let uu____5771 =
                              let uu____5786 =
                                let uu____5801 =
                                  let uu____5816 =
                                    let uu____5831 =
                                      let uu____5846 =
                                        let uu____5861 =
                                          let uu____5876 =
                                            let uu____5891 =
                                              let uu____5904 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5904,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5911 =
                                              let uu____5926 =
                                                let uu____5939 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5939,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5948 =
                                                let uu____5963 =
                                                  let uu____5978 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5978,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5987 =
                                                  let uu____6004 =
                                                    let uu____6025 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6025,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6040 =
                                                    let uu____6063 =
                                                      let uu____6082 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6082,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6095 =
                                                      let uu____6116 =
                                                        let uu____6131 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6131,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6116] in
                                                    uu____6063 :: uu____6095 in
                                                  uu____6004 :: uu____6040 in
                                                uu____5963 :: uu____5987 in
                                              uu____5926 :: uu____5948 in
                                            uu____5891 :: uu____5911 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5876 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5861 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5846 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5831 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5816 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5801 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5786 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5771 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5756 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5741 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5726 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                FStar_Syntax_Embeddings.embed_bool r (x >= y))))
                      :: uu____5711 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              FStar_Syntax_Embeddings.embed_bool r (x > y))))
                    :: uu____5696 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            FStar_Syntax_Embeddings.embed_bool r (x <= y))))
                  :: uu____5681 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          FStar_Syntax_Embeddings.embed_bool r (x < y))))
                :: uu____5666 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5651 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5636 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5621 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5606 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5591 in
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
      let uu____6720 =
        let uu____6721 =
          let uu____6722 = FStar_Syntax_Syntax.as_arg c in [uu____6722] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6721 in
      uu____6720 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6757 =
              let uu____6770 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6770, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6789  ->
                        fun uu____6790  ->
                          match (uu____6789, uu____6790) with
                          | ((int_to_t1,x),(uu____6809,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6819 =
              let uu____6834 =
                let uu____6847 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6847, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6866  ->
                          fun uu____6867  ->
                            match (uu____6866, uu____6867) with
                            | ((int_to_t1,x),(uu____6886,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6896 =
                let uu____6911 =
                  let uu____6924 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6924, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6943  ->
                            fun uu____6944  ->
                              match (uu____6943, uu____6944) with
                              | ((int_to_t1,x),(uu____6963,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6911] in
              uu____6834 :: uu____6896 in
            uu____6757 :: uu____6819)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____7062)::(a1,uu____7064)::(a2,uu____7066)::[] ->
        let uu____7103 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7103 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___215_7109 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___215_7109.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___215_7109.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___216_7113 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_7113.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_7113.FStar_Syntax_Syntax.vars)
                })
         | uu____7114 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7116)::uu____7117::(a1,uu____7119)::(a2,uu____7121)::[] ->
        let uu____7170 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7170 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___215_7176 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___215_7176.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___215_7176.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___216_7180 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_7180.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_7180.FStar_Syntax_Syntax.vars)
                })
         | uu____7181 -> FStar_Pervasives_Native.None)
    | uu____7182 -> failwith "Unexpected number of arguments" in
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
      let uu____7202 =
        let uu____7203 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____7203 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____7202
    with | uu____7209 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____7216 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7216) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7276  ->
           fun subst1  ->
             match uu____7276 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____7318)) ->
                      let uu____7377 = b in
                      (match uu____7377 with
                       | (bv,uu____7385) ->
                           let uu____7386 =
                             let uu____7387 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7387 in
                           if uu____7386
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7392 = unembed_binder term1 in
                              match uu____7392 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7399 =
                                      let uu___219_7400 = bv in
                                      let uu____7401 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___219_7400.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___219_7400.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7401
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7399 in
                                  let b_for_x =
                                    let uu____7405 =
                                      let uu____7412 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7412) in
                                    FStar_Syntax_Syntax.NT uu____7405 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___184_7421  ->
                                         match uu___184_7421 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7422,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7424;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7425;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7430 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7431 -> subst1)) env []
let reduce_primops:
  'Auu____7454 'Auu____7455 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7455) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7454 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____7496 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7496
          then tm
          else
            (let uu____7498 = FStar_Syntax_Util.head_and_args tm in
             match uu____7498 with
             | (head1,args) ->
                 let uu____7535 =
                   let uu____7536 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7536.FStar_Syntax_Syntax.n in
                 (match uu____7535 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7540 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7540 with
                       | FStar_Pervasives_Native.None  -> tm
                       | FStar_Pervasives_Native.Some prim_step ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7557  ->
                                   let uu____7558 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7559 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7566 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7558 uu____7559 uu____7566);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7571  ->
                                   let uu____7572 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7572);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7575  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7577 =
                                 prim_step.interpretation psc args in
                               match uu____7577 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7583  ->
                                         let uu____7584 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7584);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7590  ->
                                         let uu____7591 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7592 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7591 uu____7592);
                                    reduced))))
                  | uu____7593 -> tm))
let reduce_equality:
  'Auu____7604 'Auu____7605 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7605) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7604 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___220_7643 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___220_7643.tcenv);
           delta_level = (uu___220_7643.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  'Auu____7656 'Auu____7657 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7657) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7656 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7699 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7699
          then tm1
          else
            (let w t =
               let uu___221_7711 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___221_7711.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___221_7711.FStar_Syntax_Syntax.vars)
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
               | uu____7728 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7768;
                         FStar_Syntax_Syntax.vars = uu____7769;_},uu____7770);
                    FStar_Syntax_Syntax.pos = uu____7771;
                    FStar_Syntax_Syntax.vars = uu____7772;_},args)
                 ->
                 let uu____7798 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7798
                 then
                   let uu____7799 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7799 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7854)::
                        (uu____7855,(arg,uu____7857))::[] -> arg
                    | (uu____7922,(arg,uu____7924))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7925)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7990)::uu____7991::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8054::(FStar_Pervasives_Native.Some (false
                                   ),uu____8055)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8118 -> tm1)
                 else
                   (let uu____8134 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8134
                    then
                      let uu____8135 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8135 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8190)::uu____8191::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8254::(FStar_Pervasives_Native.Some (true
                                     ),uu____8255)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8318)::
                          (uu____8319,(arg,uu____8321))::[] -> arg
                      | (uu____8386,(arg,uu____8388))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8389)::[]
                          -> arg
                      | uu____8454 -> tm1
                    else
                      (let uu____8470 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8470
                       then
                         let uu____8471 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8471 with
                         | uu____8526::(FStar_Pervasives_Native.Some (true
                                        ),uu____8527)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8590)::uu____8591::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8654)::
                             (uu____8655,(arg,uu____8657))::[] -> arg
                         | (uu____8722,(p,uu____8724))::(uu____8725,(q,uu____8727))::[]
                             ->
                             let uu____8792 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8792
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8794 -> tm1
                       else
                         (let uu____8810 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8810
                          then
                            let uu____8811 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8811 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8866)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8905)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8944 -> tm1
                          else
                            (let uu____8960 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8960
                             then
                               match args with
                               | (t,uu____8962)::[] ->
                                   let uu____8979 =
                                     let uu____8980 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8980.FStar_Syntax_Syntax.n in
                                   (match uu____8979 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8983::[],body,uu____8985) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9012 -> tm1)
                                    | uu____9015 -> tm1)
                               | (uu____9016,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9017))::
                                   (t,uu____9019)::[] ->
                                   let uu____9058 =
                                     let uu____9059 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9059.FStar_Syntax_Syntax.n in
                                   (match uu____9058 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9062::[],body,uu____9064) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9091 -> tm1)
                                    | uu____9094 -> tm1)
                               | uu____9095 -> tm1
                             else
                               (let uu____9105 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9105
                                then
                                  match args with
                                  | (t,uu____9107)::[] ->
                                      let uu____9124 =
                                        let uu____9125 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9125.FStar_Syntax_Syntax.n in
                                      (match uu____9124 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9128::[],body,uu____9130)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9157 -> tm1)
                                       | uu____9160 -> tm1)
                                  | (uu____9161,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9162))::(t,uu____9164)::[] ->
                                      let uu____9203 =
                                        let uu____9204 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9204.FStar_Syntax_Syntax.n in
                                      (match uu____9203 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9207::[],body,uu____9209)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9236 -> tm1)
                                       | uu____9239 -> tm1)
                                  | uu____9240 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9251;
                    FStar_Syntax_Syntax.vars = uu____9252;_},args)
                 ->
                 let uu____9274 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9274
                 then
                   let uu____9275 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9275 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9330)::
                        (uu____9331,(arg,uu____9333))::[] -> arg
                    | (uu____9398,(arg,uu____9400))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9401)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9466)::uu____9467::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9530::(FStar_Pervasives_Native.Some (false
                                   ),uu____9531)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9594 -> tm1)
                 else
                   (let uu____9610 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9610
                    then
                      let uu____9611 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9611 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9666)::uu____9667::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9730::(FStar_Pervasives_Native.Some (true
                                     ),uu____9731)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9794)::
                          (uu____9795,(arg,uu____9797))::[] -> arg
                      | (uu____9862,(arg,uu____9864))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9865)::[]
                          -> arg
                      | uu____9930 -> tm1
                    else
                      (let uu____9946 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9946
                       then
                         let uu____9947 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9947 with
                         | uu____10002::(FStar_Pervasives_Native.Some (true
                                         ),uu____10003)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10066)::uu____10067::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10130)::
                             (uu____10131,(arg,uu____10133))::[] -> arg
                         | (uu____10198,(p,uu____10200))::(uu____10201,
                                                           (q,uu____10203))::[]
                             ->
                             let uu____10268 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10268
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____10270 -> tm1
                       else
                         (let uu____10286 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10286
                          then
                            let uu____10287 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10287 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10342)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10381)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10420 -> tm1
                          else
                            (let uu____10436 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10436
                             then
                               match args with
                               | (t,uu____10438)::[] ->
                                   let uu____10455 =
                                     let uu____10456 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10456.FStar_Syntax_Syntax.n in
                                   (match uu____10455 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10459::[],body,uu____10461) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10488 -> tm1)
                                    | uu____10491 -> tm1)
                               | (uu____10492,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10493))::
                                   (t,uu____10495)::[] ->
                                   let uu____10534 =
                                     let uu____10535 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10535.FStar_Syntax_Syntax.n in
                                   (match uu____10534 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10538::[],body,uu____10540) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10567 -> tm1)
                                    | uu____10570 -> tm1)
                               | uu____10571 -> tm1
                             else
                               (let uu____10581 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10581
                                then
                                  match args with
                                  | (t,uu____10583)::[] ->
                                      let uu____10600 =
                                        let uu____10601 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10601.FStar_Syntax_Syntax.n in
                                      (match uu____10600 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10604::[],body,uu____10606)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10633 -> tm1)
                                       | uu____10636 -> tm1)
                                  | (uu____10637,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10638))::(t,uu____10640)::[] ->
                                      let uu____10679 =
                                        let uu____10680 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10680.FStar_Syntax_Syntax.n in
                                      (match uu____10679 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10683::[],body,uu____10685)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10712 -> tm1)
                                       | uu____10715 -> tm1)
                                  | uu____10716 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | uu____10726 -> tm1)
let is_norm_request:
  'Auu____10733 .
    FStar_Syntax_Syntax.term -> 'Auu____10733 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10746 =
        let uu____10753 =
          let uu____10754 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10754.FStar_Syntax_Syntax.n in
        (uu____10753, args) in
      match uu____10746 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10760::uu____10761::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10765::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10770::uu____10771::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10774 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___185_10786  ->
    match uu___185_10786 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10792 =
          let uu____10795 =
            let uu____10796 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10796 in
          [uu____10795] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10792
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10815 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10815) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10853 =
          let uu____10856 =
            let uu____10861 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10861 s in
          FStar_All.pipe_right uu____10856 FStar_Util.must in
        FStar_All.pipe_right uu____10853 tr_norm_steps in
      match args with
      | uu____10886::(tm,uu____10888)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10911)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10926)::uu____10927::(tm,uu____10929)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10969 =
              let uu____10972 = full_norm steps in parse_steps uu____10972 in
            Beta :: uu____10969 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10981 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___186_10999  ->
    match uu___186_10999 with
    | (App
        (uu____11002,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11003;
                       FStar_Syntax_Syntax.vars = uu____11004;_},uu____11005,uu____11006))::uu____11007
        -> true
    | uu____11014 -> false
let firstn:
  'Auu____11023 .
    Prims.int ->
      'Auu____11023 Prims.list ->
        ('Auu____11023 Prims.list,'Auu____11023 Prims.list)
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
          (uu____11061,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11062;
                         FStar_Syntax_Syntax.vars = uu____11063;_},uu____11064,uu____11065))::uu____11066
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11073 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11189  ->
               let uu____11190 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11191 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11192 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11199 =
                 let uu____11200 =
                   let uu____11203 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11203 in
                 stack_to_string uu____11200 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11190 uu____11191 uu____11192 uu____11199);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11226 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11251 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11268 =
                 let uu____11269 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11270 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11269 uu____11270 in
               failwith uu____11268
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11271 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____11288 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____11289 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11290;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11291;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11294;
                 FStar_Syntax_Syntax.fv_delta = uu____11295;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11296;
                 FStar_Syntax_Syntax.fv_delta = uu____11297;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11298);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11306 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11306 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____11312  ->
                     let uu____11313 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11314 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11313 uu____11314);
                if b
                then
                  (let uu____11315 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____11315 t1 fv)
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
                 let uu___222_11354 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___222_11354.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___222_11354.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11387 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11387) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___223_11395 = cfg in
                 let uu____11396 =
                   FStar_List.filter
                     (fun uu___187_11399  ->
                        match uu___187_11399 with
                        | UnfoldOnly uu____11400 -> false
                        | NoDeltaSteps  -> false
                        | uu____11403 -> true) cfg.steps in
                 {
                   steps = uu____11396;
                   tcenv = (uu___223_11395.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___223_11395.primitive_steps)
                 } in
               let uu____11404 = get_norm_request (norm cfg' env []) args in
               (match uu____11404 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11420 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___188_11425  ->
                                match uu___188_11425 with
                                | UnfoldUntil uu____11426 -> true
                                | UnfoldOnly uu____11427 -> true
                                | uu____11430 -> false)) in
                      if uu____11420
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___224_11435 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___224_11435.tcenv);
                        delta_level;
                        primitive_steps = (uu___224_11435.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11446 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11446
                      then
                        let uu____11449 =
                          let uu____11450 =
                            let uu____11455 = FStar_Util.now () in
                            (t1, uu____11455) in
                          Debug uu____11450 in
                        uu____11449 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11457;
                  FStar_Syntax_Syntax.vars = uu____11458;_},a1::a2::rest)
               ->
               let uu____11506 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11506 with
                | (hd1,uu____11522) ->
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
                    (FStar_Const.Const_reflect uu____11587);
                  FStar_Syntax_Syntax.pos = uu____11588;
                  FStar_Syntax_Syntax.vars = uu____11589;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11621 = FStar_List.tl stack1 in
               norm cfg env uu____11621 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11624;
                  FStar_Syntax_Syntax.vars = uu____11625;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11657 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11657 with
                | (reify_head,uu____11673) ->
                    let a1 =
                      let uu____11695 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11695 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11698);
                            FStar_Syntax_Syntax.pos = uu____11699;
                            FStar_Syntax_Syntax.vars = uu____11700;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11734 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11744 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11744
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11751 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11751
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11754 =
                      let uu____11761 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11761, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11754 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___189_11774  ->
                         match uu___189_11774 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11777 =
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
                 if uu____11777
                 then false
                 else
                   (let uu____11779 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___190_11786  ->
                              match uu___190_11786 with
                              | UnfoldOnly uu____11787 -> true
                              | uu____11790 -> false)) in
                    match uu____11779 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11794 -> should_delta) in
               (log cfg
                  (fun uu____11802  ->
                     let uu____11803 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11804 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11805 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11803 uu____11804 uu____11805);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11808 = lookup_bvar env x in
               (match uu____11808 with
                | Univ uu____11811 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11860 = FStar_ST.op_Bang r in
                      (match uu____11860 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11997  ->
                                 let uu____11998 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11999 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11998
                                   uu____11999);
                            (let uu____12000 =
                               let uu____12001 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12001.FStar_Syntax_Syntax.n in
                             match uu____12000 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12004 ->
                                 norm cfg env2 stack1 t'
                             | uu____12021 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____12079)::uu____12080 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12089)::uu____12090 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12100,uu____12101))::stack_rest ->
                    (match c with
                     | Univ uu____12105 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12114 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12135  ->
                                    let uu____12136 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12136);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12176  ->
                                    let uu____12177 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12177);
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
                      (let uu___225_12227 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___225_12227.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12312  ->
                          let uu____12313 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12313);
                     norm cfg env stack2 t1)
                | (Debug uu____12314)::uu____12315 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12322 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12322
                    else
                      (let uu____12324 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12324 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12366  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12394 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12394
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12404 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12404)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12409 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12409.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12409.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12410 -> lopt in
                           (log cfg
                              (fun uu____12416  ->
                                 let uu____12417 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12417);
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
                | (Meta uu____12440)::uu____12441 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12448 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12448
                    else
                      (let uu____12450 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12450 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12492  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12520 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12520
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12530 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12530)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12535 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12535.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12535.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12536 -> lopt in
                           (log cfg
                              (fun uu____12542  ->
                                 let uu____12543 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12543);
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
                | (Let uu____12566)::uu____12567 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12578 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12578
                    else
                      (let uu____12580 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12580 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12622  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12650 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12650
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12660 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12660)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12665 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12665.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12665.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12666 -> lopt in
                           (log cfg
                              (fun uu____12672  ->
                                 let uu____12673 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12673);
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
                | (App uu____12696)::uu____12697 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12708 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12708
                    else
                      (let uu____12710 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12710 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12752  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12780 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12780
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12790 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12790)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12795 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12795.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12795.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12796 -> lopt in
                           (log cfg
                              (fun uu____12802  ->
                                 let uu____12803 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12803);
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
                | (Abs uu____12826)::uu____12827 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12842 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12842
                    else
                      (let uu____12844 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12844 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12886  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12914 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12914
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12924 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12924)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_12929 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_12929.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_12929.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12930 -> lopt in
                           (log cfg
                              (fun uu____12936  ->
                                 let uu____12937 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12937);
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
                      let uu____12960 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12960
                    else
                      (let uu____12962 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12962 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13004  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13032 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13032
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13042 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13042)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___226_13047 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___226_13047.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___226_13047.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13048 -> lopt in
                           (log cfg
                              (fun uu____13054  ->
                                 let uu____13055 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13055);
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
                      (fun uu____13116  ->
                         fun stack2  ->
                           match uu____13116 with
                           | (a,aq) ->
                               let uu____13128 =
                                 let uu____13129 =
                                   let uu____13136 =
                                     let uu____13137 =
                                       let uu____13168 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13168, false) in
                                     Clos uu____13137 in
                                   (uu____13136, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13129 in
                               uu____13128 :: stack2) args) in
               (log cfg
                  (fun uu____13244  ->
                     let uu____13245 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13245);
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
                             ((let uu___227_13281 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___227_13281.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___227_13281.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____13282 ->
                      let uu____13287 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13287)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13290 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13290 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13321 =
                          let uu____13322 =
                            let uu____13329 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___228_13331 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___228_13331.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___228_13331.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13329) in
                          FStar_Syntax_Syntax.Tm_refine uu____13322 in
                        mk uu____13321 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13350 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____13350
               else
                 (let uu____13352 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13352 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13360 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13384  -> dummy :: env1) env) in
                        norm_comp cfg uu____13360 c1 in
                      let t2 =
                        let uu____13406 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13406 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13465)::uu____13466 ->
                    (log cfg
                       (fun uu____13477  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13478)::uu____13479 ->
                    (log cfg
                       (fun uu____13490  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13491,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13492;
                                   FStar_Syntax_Syntax.vars = uu____13493;_},uu____13494,uu____13495))::uu____13496
                    ->
                    (log cfg
                       (fun uu____13505  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13506)::uu____13507 ->
                    (log cfg
                       (fun uu____13518  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13519 ->
                    (log cfg
                       (fun uu____13522  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13526  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13543 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13543
                         | FStar_Util.Inr c ->
                             let uu____13551 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13551 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13557 =
                         let uu____13558 =
                           let uu____13559 =
                             let uu____13586 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13586, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13559 in
                         mk uu____13558 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13557))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13662,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13663;
                               FStar_Syntax_Syntax.lbunivs = uu____13664;
                               FStar_Syntax_Syntax.lbtyp = uu____13665;
                               FStar_Syntax_Syntax.lbeff = uu____13666;
                               FStar_Syntax_Syntax.lbdef = uu____13667;_}::uu____13668),uu____13669)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13705 =
                 (let uu____13708 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13708) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13710 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13710))) in
               if uu____13705
               then
                 let binder =
                   let uu____13712 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13712 in
                 let env1 =
                   let uu____13722 =
                     let uu____13729 =
                       let uu____13730 =
                         let uu____13761 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13761,
                           false) in
                       Clos uu____13730 in
                     ((FStar_Pervasives_Native.Some binder), uu____13729) in
                   uu____13722 :: env in
                 (log cfg
                    (fun uu____13846  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13848 =
                    let uu____13853 =
                      let uu____13854 =
                        let uu____13855 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13855
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13854] in
                    FStar_Syntax_Subst.open_term uu____13853 body in
                  match uu____13848 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13864  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13872 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13872 in
                          FStar_Util.Inl
                            (let uu___229_13882 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___229_13882.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___229_13882.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13885  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___230_13887 = lb in
                           let uu____13888 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___230_13887.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___230_13887.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13888
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13923  -> dummy :: env1) env) in
                         let cfg1 = only_strong_steps cfg in
                         log cfg1
                           (fun uu____13945  ->
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
               let uu____13962 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13962 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13998 =
                               let uu___231_13999 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___231_13999.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___231_13999.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13998 in
                           let uu____14000 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14000 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14026 =
                                   FStar_List.map (fun uu____14042  -> dummy)
                                     lbs1 in
                                 let uu____14043 =
                                   let uu____14052 =
                                     FStar_List.map
                                       (fun uu____14072  -> dummy) xs1 in
                                   FStar_List.append uu____14052 env in
                                 FStar_List.append uu____14026 uu____14043 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14096 =
                                       let uu___232_14097 = rc in
                                       let uu____14098 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___232_14097.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14098;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___232_14097.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14096
                                 | uu____14105 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___233_14109 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___233_14109.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___233_14109.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14119 =
                        FStar_List.map (fun uu____14135  -> dummy) lbs2 in
                      FStar_List.append uu____14119 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14143 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14143 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___234_14159 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___234_14159.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___234_14159.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14186 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____14186
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14205 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14281  ->
                        match uu____14281 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___235_14402 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___235_14402.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___235_14402.FStar_Syntax_Syntax.sort)
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
               (match uu____14205 with
                | (rec_env,memos,uu____14599) ->
                    let uu____14652 =
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
                             let uu____15183 =
                               let uu____15190 =
                                 let uu____15191 =
                                   let uu____15222 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15222, false) in
                                 Clos uu____15191 in
                               (FStar_Pervasives_Native.None, uu____15190) in
                             uu____15183 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15327 =
                      let uu____15328 = should_reify cfg stack1 in
                      Prims.op_Negation uu____15328 in
                    if uu____15327
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____15338 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15338
                        then
                          let uu___236_15339 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___236_15339.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___236_15339.primitive_steps)
                          }
                        else
                          (let uu___237_15341 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___237_15341.tcenv);
                             delta_level = (uu___237_15341.delta_level);
                             primitive_steps =
                               (uu___237_15341.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____15343 =
                         let uu____15344 = FStar_Syntax_Subst.compress head1 in
                         uu____15344.FStar_Syntax_Syntax.n in
                       match uu____15343 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15362 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15362 with
                            | (uu____15363,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15369 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15377 =
                                         let uu____15378 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15378.FStar_Syntax_Syntax.n in
                                       match uu____15377 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15384,uu____15385))
                                           ->
                                           let uu____15394 =
                                             let uu____15395 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15395.FStar_Syntax_Syntax.n in
                                           (match uu____15394 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15401,msrc,uu____15403))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15412 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15412
                                            | uu____15413 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15414 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15415 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15415 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___238_15420 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___238_15420.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___238_15420.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___238_15420.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15421 =
                                            FStar_List.tl stack1 in
                                          let uu____15422 =
                                            let uu____15423 =
                                              let uu____15426 =
                                                let uu____15427 =
                                                  let uu____15440 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15440) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15427 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15426 in
                                            uu____15423
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15421
                                            uu____15422
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15456 =
                                            let uu____15457 = is_return body in
                                            match uu____15457 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15461;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15462;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15467 -> false in
                                          if uu____15456
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
                                               let uu____15491 =
                                                 let uu____15494 =
                                                   let uu____15495 =
                                                     let uu____15512 =
                                                       let uu____15515 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15515] in
                                                     (uu____15512, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15495 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15494 in
                                               uu____15491
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15531 =
                                                 let uu____15532 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15532.FStar_Syntax_Syntax.n in
                                               match uu____15531 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15538::uu____15539::[])
                                                   ->
                                                   let uu____15546 =
                                                     let uu____15549 =
                                                       let uu____15550 =
                                                         let uu____15557 =
                                                           let uu____15560 =
                                                             let uu____15561
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15561 in
                                                           let uu____15562 =
                                                             let uu____15565
                                                               =
                                                               let uu____15566
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15566 in
                                                             [uu____15565] in
                                                           uu____15560 ::
                                                             uu____15562 in
                                                         (bind1, uu____15557) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15550 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15549 in
                                                   uu____15546
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15574 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15580 =
                                                 let uu____15583 =
                                                   let uu____15584 =
                                                     let uu____15599 =
                                                       let uu____15602 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15603 =
                                                         let uu____15606 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15607 =
                                                           let uu____15610 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15611 =
                                                             let uu____15614
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15615
                                                               =
                                                               let uu____15618
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15619
                                                                 =
                                                                 let uu____15622
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15622] in
                                                               uu____15618 ::
                                                                 uu____15619 in
                                                             uu____15614 ::
                                                               uu____15615 in
                                                           uu____15610 ::
                                                             uu____15611 in
                                                         uu____15606 ::
                                                           uu____15607 in
                                                       uu____15602 ::
                                                         uu____15603 in
                                                     (bind_inst, uu____15599) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15584 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15583 in
                                               uu____15580
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15630 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15630 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15654 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15654 with
                            | (uu____15655,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15690 =
                                        let uu____15691 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15691.FStar_Syntax_Syntax.n in
                                      match uu____15690 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15697) -> t4
                                      | uu____15702 -> head2 in
                                    let uu____15703 =
                                      let uu____15704 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15704.FStar_Syntax_Syntax.n in
                                    match uu____15703 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15710 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15711 = maybe_extract_fv head2 in
                                  match uu____15711 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15721 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15721
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15726 =
                                          maybe_extract_fv head3 in
                                        match uu____15726 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15731 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15732 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15737 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15752 =
                                    match uu____15752 with
                                    | (e,q) ->
                                        let uu____15759 =
                                          let uu____15760 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15760.FStar_Syntax_Syntax.n in
                                        (match uu____15759 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15775 -> false) in
                                  let uu____15776 =
                                    let uu____15777 =
                                      let uu____15784 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15784 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15777 in
                                  if uu____15776
                                  then
                                    let uu____15789 =
                                      let uu____15790 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15790 in
                                    failwith uu____15789
                                  else ());
                                 (let uu____15792 =
                                    maybe_unfold_action head_app in
                                  match uu____15792 with
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
                                      let uu____15831 = FStar_List.tl stack1 in
                                      norm cfg env uu____15831 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15845 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15845 in
                           let uu____15846 = FStar_List.tl stack1 in
                           norm cfg env uu____15846 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15967  ->
                                     match uu____15967 with
                                     | (pat,wopt,tm) ->
                                         let uu____16015 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16015))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16047 = FStar_List.tl stack1 in
                           norm cfg env uu____16047 tm
                       | uu____16048 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16056 = should_reify cfg stack1 in
                    if uu____16056
                    then
                      let uu____16057 = FStar_List.tl stack1 in
                      let uu____16058 =
                        let uu____16059 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16059 in
                      norm cfg env uu____16057 uu____16058
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16062 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16062
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___239_16071 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___239_16071.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___239_16071.primitive_steps)
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
                | uu____16073 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____16075::uu____16076 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16081) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16082 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____16113 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16127 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16127
                             | uu____16138 -> m in
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
              let uu____16150 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16150 in
            let uu____16151 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16151 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16164  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16175  ->
                      let uu____16176 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16177 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16176
                        uu____16177);
                 (let t1 =
                    let uu____16179 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16179
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
                    | (UnivArgs (us',uu____16189))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____16244 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____16247 ->
                        let uu____16250 =
                          let uu____16251 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16251 in
                        failwith uu____16250
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
              let uu____16261 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16261 with
              | (uu____16262,return_repr) ->
                  let return_inst =
                    let uu____16271 =
                      let uu____16272 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16272.FStar_Syntax_Syntax.n in
                    match uu____16271 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16278::[]) ->
                        let uu____16285 =
                          let uu____16288 =
                            let uu____16289 =
                              let uu____16296 =
                                let uu____16299 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16299] in
                              (return_tm, uu____16296) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16289 in
                          FStar_Syntax_Syntax.mk uu____16288 in
                        uu____16285 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16307 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16310 =
                    let uu____16313 =
                      let uu____16314 =
                        let uu____16329 =
                          let uu____16332 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16333 =
                            let uu____16336 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16336] in
                          uu____16332 :: uu____16333 in
                        (return_inst, uu____16329) in
                      FStar_Syntax_Syntax.Tm_app uu____16314 in
                    FStar_Syntax_Syntax.mk uu____16313 in
                  uu____16310 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16345 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16345 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16348 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16348
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16349;
                     FStar_TypeChecker_Env.mtarget = uu____16350;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16351;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16362;
                     FStar_TypeChecker_Env.mtarget = uu____16363;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16364;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16382 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16382)
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
                (fun uu____16438  ->
                   match uu____16438 with
                   | (a,imp) ->
                       let uu____16449 = norm cfg env [] a in
                       (uu____16449, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___240_16466 = comp1 in
            let uu____16469 =
              let uu____16470 =
                let uu____16479 = norm cfg env [] t in
                let uu____16480 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16479, uu____16480) in
              FStar_Syntax_Syntax.Total uu____16470 in
            {
              FStar_Syntax_Syntax.n = uu____16469;
              FStar_Syntax_Syntax.pos =
                (uu___240_16466.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___240_16466.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___241_16495 = comp1 in
            let uu____16498 =
              let uu____16499 =
                let uu____16508 = norm cfg env [] t in
                let uu____16509 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16508, uu____16509) in
              FStar_Syntax_Syntax.GTotal uu____16499 in
            {
              FStar_Syntax_Syntax.n = uu____16498;
              FStar_Syntax_Syntax.pos =
                (uu___241_16495.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___241_16495.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16561  ->
                      match uu____16561 with
                      | (a,i) ->
                          let uu____16572 = norm cfg env [] a in
                          (uu____16572, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___191_16583  ->
                      match uu___191_16583 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16587 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16587
                      | f -> f)) in
            let uu___242_16591 = comp1 in
            let uu____16594 =
              let uu____16595 =
                let uu___243_16596 = ct in
                let uu____16597 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16598 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16601 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16597;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___243_16596.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16598;
                  FStar_Syntax_Syntax.effect_args = uu____16601;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16595 in
            {
              FStar_Syntax_Syntax.n = uu____16594;
              FStar_Syntax_Syntax.pos =
                (uu___242_16591.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___242_16591.FStar_Syntax_Syntax.vars)
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
            (let uu___244_16619 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___244_16619.tcenv);
               delta_level = (uu___244_16619.delta_level);
               primitive_steps = (uu___244_16619.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____16624 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16624 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16627 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___245_16646 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___245_16646.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___245_16646.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16653 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16653
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
                    let uu___246_16664 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___246_16664.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___246_16664.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___246_16664.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___247_16666 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___247_16666.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___247_16666.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___247_16666.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___247_16666.FStar_Syntax_Syntax.flags)
                    } in
              let uu___248_16667 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___248_16667.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___248_16667.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16669 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16672  ->
        match uu____16672 with
        | (x,imp) ->
            let uu____16675 =
              let uu___249_16676 = x in
              let uu____16677 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___249_16676.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___249_16676.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16677
              } in
            (uu____16675, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16683 =
          FStar_List.fold_left
            (fun uu____16701  ->
               fun b  ->
                 match uu____16701 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16683 with | (nbs,uu____16741) -> FStar_List.rev nbs
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
            let uu____16757 =
              let uu___250_16758 = rc in
              let uu____16759 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___250_16758.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16759;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___250_16758.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16757
        | uu____16766 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16779  ->
               let uu____16780 = FStar_Syntax_Print.tag_of_term t in
               let uu____16781 = FStar_Syntax_Print.term_to_string t in
               let uu____16782 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16789 =
                 let uu____16790 =
                   let uu____16793 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16793 in
                 stack_to_string uu____16790 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16780 uu____16781 uu____16782 uu____16789);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16822 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16822
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16824 =
                     let uu____16825 =
                       let uu____16826 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16826 in
                     FStar_Util.string_of_int uu____16825 in
                   let uu____16831 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16832 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16824 uu____16831 uu____16832
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___251_16850 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___251_16850.tcenv);
                    delta_level = dl;
                    primitive_steps = ps
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16943  ->
                     let uu____16944 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16944);
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
               let uu____16980 =
                 let uu___252_16981 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___252_16981.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___252_16981.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16980
           | (Arg (Univ uu____16982,uu____16983,uu____16984))::uu____16985 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16988,uu____16989))::uu____16990 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____17006),aq,r))::stack2 ->
               (log cfg
                  (fun uu____17059  ->
                     let uu____17060 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17060);
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
                  (let uu____17070 = FStar_ST.op_Bang m in
                   match uu____17070 with
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
                   | FStar_Pervasives_Native.Some (uu____17214,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17257 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____17257
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____17269  ->
                     let uu____17270 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17270);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17275 =
                   log cfg
                     (fun uu____17280  ->
                        let uu____17281 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17282 =
                          let uu____17283 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17300  ->
                                    match uu____17300 with
                                    | (p,uu____17310,uu____17311) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17283
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17281 uu____17282);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___192_17328  ->
                                match uu___192_17328 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17329 -> false)) in
                      let steps' =
                        let uu____17333 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____17333
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      only_strong_steps
                        (let uu___253_17339 = cfg in
                         {
                           steps = (FStar_List.append steps' cfg.steps);
                           tcenv = (uu___253_17339.tcenv);
                           delta_level = new_delta;
                           primitive_steps = (uu___253_17339.primitive_steps)
                         }) in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17371 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17392 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17452  ->
                                    fun uu____17453  ->
                                      match (uu____17452, uu____17453) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17544 = norm_pat env3 p1 in
                                          (match uu____17544 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17392 with
                           | (pats1,env3) ->
                               ((let uu___254_17626 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___254_17626.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___255_17645 = x in
                            let uu____17646 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___255_17645.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___255_17645.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17646
                            } in
                          ((let uu___256_17660 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___256_17660.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___257_17671 = x in
                            let uu____17672 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___257_17671.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___257_17671.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17672
                            } in
                          ((let uu___258_17686 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___258_17686.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___259_17702 = x in
                            let uu____17703 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___259_17702.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___259_17702.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17703
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___260_17710 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___260_17710.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17720 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17734 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17734 with
                                  | (p,wopt,e) ->
                                      let uu____17754 = norm_pat env1 p in
                                      (match uu____17754 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17779 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17779 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17785 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17785) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17795) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17800 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17801;
                         FStar_Syntax_Syntax.fv_delta = uu____17802;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17803;
                         FStar_Syntax_Syntax.fv_delta = uu____17804;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17805);_}
                       -> true
                   | uu____17812 -> false in
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
                   let uu____17957 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17957 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18044 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____18083 ->
                                 let uu____18084 =
                                   let uu____18085 = is_cons head1 in
                                   Prims.op_Negation uu____18085 in
                                 FStar_Util.Inr uu____18084)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18110 =
                              let uu____18111 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18111.FStar_Syntax_Syntax.n in
                            (match uu____18110 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18129 ->
                                 let uu____18130 =
                                   let uu____18131 = is_cons head1 in
                                   Prims.op_Negation uu____18131 in
                                 FStar_Util.Inr uu____18130))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18200)::rest_a,(p1,uu____18203)::rest_p) ->
                       let uu____18247 = matches_pat t1 p1 in
                       (match uu____18247 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18296 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18402 = matches_pat scrutinee1 p1 in
                       (match uu____18402 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18442  ->
                                  let uu____18443 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18444 =
                                    let uu____18445 =
                                      FStar_List.map
                                        (fun uu____18455  ->
                                           match uu____18455 with
                                           | (uu____18460,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18445
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18443 uu____18444);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18491  ->
                                       match uu____18491 with
                                       | (bv,t1) ->
                                           let uu____18514 =
                                             let uu____18521 =
                                               let uu____18524 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18524 in
                                             let uu____18525 =
                                               let uu____18526 =
                                                 let uu____18557 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18557, false) in
                                               Clos uu____18526 in
                                             (uu____18521, uu____18525) in
                                           uu____18514 :: env2) env1 s in
                              let uu____18666 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18666))) in
                 let uu____18667 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18667
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___193_18690  ->
                match uu___193_18690 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18694 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18700 -> d in
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
            let uu___261_18729 = config s e in
            {
              steps = (uu___261_18729.steps);
              tcenv = (uu___261_18729.tcenv);
              delta_level = (uu___261_18729.delta_level);
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
      fun t  -> let uu____18760 = config s e in norm_comp uu____18760 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18775 = config [] env in norm_universe uu____18775 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18790 = config [] env in ghost_to_pure_aux uu____18790 [] c
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
        let uu____18810 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18810 in
      let uu____18817 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18817
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___262_18819 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___262_18819.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___262_18819.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18822  ->
                    let uu____18823 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18823))
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
            ((let uu____18842 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18842);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18855 = config [AllowUnboundUniverses] env in
          norm_comp uu____18855 [] c
        with
        | e ->
            ((let uu____18868 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18868);
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
                   let uu____18908 =
                     let uu____18909 =
                       let uu____18916 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18916) in
                     FStar_Syntax_Syntax.Tm_refine uu____18909 in
                   mk uu____18908 t01.FStar_Syntax_Syntax.pos
               | uu____18921 -> t2)
          | uu____18922 -> t2 in
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
        let uu____18974 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18974 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19003 ->
                 let uu____19010 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19010 with
                  | (actuals,uu____19020,uu____19021) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19035 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19035 with
                         | (binders,args) ->
                             let uu____19052 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19052
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
      | uu____19062 ->
          let uu____19063 = FStar_Syntax_Util.head_and_args t in
          (match uu____19063 with
           | (head1,args) ->
               let uu____19100 =
                 let uu____19101 = FStar_Syntax_Subst.compress head1 in
                 uu____19101.FStar_Syntax_Syntax.n in
               (match uu____19100 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19104,thead) ->
                    let uu____19130 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19130 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19172 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___267_19180 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___267_19180.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___267_19180.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___267_19180.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___267_19180.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___267_19180.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___267_19180.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___267_19180.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___267_19180.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___267_19180.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___267_19180.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___267_19180.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___267_19180.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___267_19180.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___267_19180.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___267_19180.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___267_19180.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___267_19180.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___267_19180.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___267_19180.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___267_19180.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___267_19180.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___267_19180.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___267_19180.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___267_19180.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___267_19180.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___267_19180.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___267_19180.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___267_19180.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___267_19180.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___267_19180.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____19172 with
                            | (uu____19181,ty,uu____19183) ->
                                eta_expand_with_type env t ty))
                | uu____19184 ->
                    let uu____19185 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___268_19193 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___268_19193.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___268_19193.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___268_19193.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___268_19193.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___268_19193.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___268_19193.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___268_19193.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___268_19193.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___268_19193.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___268_19193.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___268_19193.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___268_19193.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___268_19193.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___268_19193.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___268_19193.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___268_19193.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___268_19193.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___268_19193.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___268_19193.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___268_19193.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___268_19193.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___268_19193.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___268_19193.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___268_19193.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___268_19193.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___268_19193.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___268_19193.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___268_19193.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___268_19193.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___268_19193.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____19185 with
                     | (uu____19194,ty,uu____19196) ->
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
            | (uu____19274,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19280,FStar_Util.Inl t) ->
                let uu____19286 =
                  let uu____19289 =
                    let uu____19290 =
                      let uu____19303 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19303) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19290 in
                  FStar_Syntax_Syntax.mk uu____19289 in
                uu____19286 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19307 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19307 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19334 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19389 ->
                    let uu____19390 =
                      let uu____19399 =
                        let uu____19400 = FStar_Syntax_Subst.compress t3 in
                        uu____19400.FStar_Syntax_Syntax.n in
                      (uu____19399, tc) in
                    (match uu____19390 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19425) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19462) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19501,FStar_Util.Inl uu____19502) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19525 -> failwith "Impossible") in
              (match uu____19334 with
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
          let uu____19634 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19634 with
          | (univ_names1,binders1,tc) ->
              let uu____19692 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19692)
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
          let uu____19731 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19731 with
          | (univ_names1,binders1,tc) ->
              let uu____19791 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19791)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19826 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19826 with
           | (univ_names1,binders1,typ1) ->
               let uu___269_19854 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___269_19854.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___269_19854.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___269_19854.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___269_19854.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___270_19875 = s in
          let uu____19876 =
            let uu____19877 =
              let uu____19886 = FStar_List.map (elim_uvars env) sigs in
              (uu____19886, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19877 in
          {
            FStar_Syntax_Syntax.sigel = uu____19876;
            FStar_Syntax_Syntax.sigrng =
              (uu___270_19875.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___270_19875.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___270_19875.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___270_19875.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19903 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19903 with
           | (univ_names1,uu____19921,typ1) ->
               let uu___271_19935 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___271_19935.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___271_19935.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___271_19935.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___271_19935.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19941 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19941 with
           | (univ_names1,uu____19959,typ1) ->
               let uu___272_19973 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___272_19973.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___272_19973.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___272_19973.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___272_19973.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20007 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20007 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20030 =
                            let uu____20031 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20031 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20030 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___273_20034 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___273_20034.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___273_20034.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___274_20035 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___274_20035.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___274_20035.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___274_20035.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___274_20035.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___275_20047 = s in
          let uu____20048 =
            let uu____20049 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20049 in
          {
            FStar_Syntax_Syntax.sigel = uu____20048;
            FStar_Syntax_Syntax.sigrng =
              (uu___275_20047.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___275_20047.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___275_20047.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___275_20047.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20053 = elim_uvars_aux_t env us [] t in
          (match uu____20053 with
           | (us1,uu____20071,t1) ->
               let uu___276_20085 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___276_20085.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___276_20085.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___276_20085.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___276_20085.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20086 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20088 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20088 with
           | (univs1,binders,signature) ->
               let uu____20116 =
                 let uu____20125 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20125 with
                 | (univs_opening,univs2) ->
                     let uu____20152 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20152) in
               (match uu____20116 with
                | (univs_opening,univs_closing) ->
                    let uu____20169 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20175 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20176 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20175, uu____20176) in
                    (match uu____20169 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20198 =
                           match uu____20198 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20216 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20216 with
                                | (us1,t1) ->
                                    let uu____20227 =
                                      let uu____20232 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20239 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20232, uu____20239) in
                                    (match uu____20227 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20252 =
                                           let uu____20257 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20266 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20257, uu____20266) in
                                         (match uu____20252 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20282 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20282 in
                                              let uu____20283 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20283 with
                                               | (uu____20304,uu____20305,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20320 =
                                                       let uu____20321 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20321 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20320 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20326 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20326 with
                           | (uu____20339,uu____20340,t1) -> t1 in
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
                             | uu____20400 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20417 =
                               let uu____20418 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20418.FStar_Syntax_Syntax.n in
                             match uu____20417 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20477 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20506 =
                               let uu____20507 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20507.FStar_Syntax_Syntax.n in
                             match uu____20506 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20528) ->
                                 let uu____20549 = destruct_action_body body in
                                 (match uu____20549 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20594 ->
                                 let uu____20595 = destruct_action_body t in
                                 (match uu____20595 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20644 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20644 with
                           | (action_univs,t) ->
                               let uu____20653 = destruct_action_typ_templ t in
                               (match uu____20653 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___277_20694 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___277_20694.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___277_20694.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___278_20696 = ed in
                           let uu____20697 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20698 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20699 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20700 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20701 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20702 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20703 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20704 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20705 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20706 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20707 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20708 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20709 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20710 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___278_20696.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___278_20696.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20697;
                             FStar_Syntax_Syntax.bind_wp = uu____20698;
                             FStar_Syntax_Syntax.if_then_else = uu____20699;
                             FStar_Syntax_Syntax.ite_wp = uu____20700;
                             FStar_Syntax_Syntax.stronger = uu____20701;
                             FStar_Syntax_Syntax.close_wp = uu____20702;
                             FStar_Syntax_Syntax.assert_p = uu____20703;
                             FStar_Syntax_Syntax.assume_p = uu____20704;
                             FStar_Syntax_Syntax.null_wp = uu____20705;
                             FStar_Syntax_Syntax.trivial = uu____20706;
                             FStar_Syntax_Syntax.repr = uu____20707;
                             FStar_Syntax_Syntax.return_repr = uu____20708;
                             FStar_Syntax_Syntax.bind_repr = uu____20709;
                             FStar_Syntax_Syntax.actions = uu____20710
                           } in
                         let uu___279_20713 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___279_20713.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___279_20713.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___279_20713.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___279_20713.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___194_20730 =
            match uu___194_20730 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20757 = elim_uvars_aux_t env us [] t in
                (match uu____20757 with
                 | (us1,uu____20781,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___280_20800 = sub_eff in
            let uu____20801 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20804 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___280_20800.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___280_20800.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20801;
              FStar_Syntax_Syntax.lift = uu____20804
            } in
          let uu___281_20807 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___281_20807.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___281_20807.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___281_20807.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___281_20807.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20817 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20817 with
           | (univ_names1,binders1,comp1) ->
               let uu___282_20851 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___282_20851.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___282_20851.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___282_20851.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___282_20851.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20862 -> s