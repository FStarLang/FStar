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
  psc_subst: FStar_Syntax_Syntax.subst_t;}[@@deriving show]
let __proj__Mkpsc__item__psc_range: psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let __proj__Mkpsc__item__psc_subst: psc -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let null_psc: psc = { psc_range = FStar_Range.dummyRange; psc_subst = [] }
let psc_range: psc -> FStar_Range.range = fun psc  -> psc.psc_range
let psc_subst: psc -> FStar_Syntax_Syntax.subst_t = fun psc  -> psc.psc_subst
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
    match projectee with | Clos _0 -> true | uu____388 -> false
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
    match projectee with | Univ _0 -> true | uu____492 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____505 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___169_525  ->
    match uu___169_525 with
    | Clos (uu____526,t,uu____528,uu____529) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____574 -> "Univ"
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
    let uu___186_667 = cfg in
    let uu____668 = only_strong_steps' cfg.primitive_steps in
    {
      steps = (uu___186_667.steps);
      tcenv = (uu___186_667.tcenv);
      delta_level = (uu___186_667.delta_level);
      primitive_steps = uu____668
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
    match projectee with | Arg _0 -> true | uu____815 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____853 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____891 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____950 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____994 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1052 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1094 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1128 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1176 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1224 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1253 .
    'Auu____1253 ->
      FStar_Range.range -> 'Auu____1253 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1410 'Auu____1411 .
    ('Auu____1411 FStar_Pervasives_Native.option,'Auu____1410) FStar_ST.mref
      -> 'Auu____1411 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1706 = FStar_ST.op_Bang r in
      match uu____1706 with
      | FStar_Pervasives_Native.Some uu____1807 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1914 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1914 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___170_1922  ->
    match uu___170_1922 with
    | Arg (c,uu____1924,uu____1925) ->
        let uu____1926 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1926
    | MemoLazy uu____1927 -> "MemoLazy"
    | Abs (uu____1934,bs,uu____1936,uu____1937,uu____1938) ->
        let uu____1943 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1943
    | UnivArgs uu____1948 -> "UnivArgs"
    | Match uu____1955 -> "Match"
    | App (uu____1962,t,uu____1964,uu____1965) ->
        let uu____1966 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1966
    | Meta (m,uu____1968) -> "Meta"
    | Let uu____1969 -> "Let"
    | Steps (uu____1978,uu____1979,uu____1980) -> "Steps"
    | Debug (t,uu____1990) ->
        let uu____1991 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1991
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____2000 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____2000 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____2018 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____2018 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____2033 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____2033 then f () else ()
let is_empty: 'Auu____2039 . 'Auu____2039 Prims.list -> Prims.bool =
  fun uu___171_2045  ->
    match uu___171_2045 with | [] -> true | uu____2048 -> false
let lookup_bvar:
  'Auu____2059 'Auu____2060 .
    ('Auu____2060,'Auu____2059) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2059
  =
  fun env  ->
    fun x  ->
      try
        let uu____2084 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____2084
      with
      | uu____2097 ->
          let uu____2098 =
            let uu____2099 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____2099 in
          failwith uu____2098
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
          let uu____2140 =
            FStar_List.fold_left
              (fun uu____2166  ->
                 fun u1  ->
                   match uu____2166 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2191 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____2191 with
                        | (k_u,n1) ->
                            let uu____2206 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2206
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____2140 with
          | (uu____2224,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2249 =
                   let uu____2250 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____2250 in
                 match uu____2249 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2268 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2277 ->
                   let uu____2278 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2278
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2284 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2293 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2302 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2309 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2309 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2326 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2326 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2334 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2342 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2342 with
                                  | (uu____2347,m) -> n1 <= m)) in
                        if uu____2334 then rest1 else us1
                    | uu____2352 -> us1)
               | uu____2357 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2361 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2361 in
        let uu____2364 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2364
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2366 = aux u in
           match uu____2366 with
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
          (fun uu____2470  ->
             let uu____2471 = FStar_Syntax_Print.tag_of_term t in
             let uu____2472 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2471
               uu____2472);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2479 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2481 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2506 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2507 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2508 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2509 ->
                  let uu____2526 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2526
                  then
                    let uu____2527 =
                      let uu____2528 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2529 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2528 uu____2529 in
                    failwith uu____2527
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2532 =
                    let uu____2533 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2533 in
                  mk uu____2532 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2540 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2540
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2542 = lookup_bvar env x in
                  (match uu____2542 with
                   | Univ uu____2545 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2549) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2661 = closures_as_binders_delayed cfg env bs in
                  (match uu____2661 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2689 =
                         let uu____2690 =
                           let uu____2707 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2707) in
                         FStar_Syntax_Syntax.Tm_abs uu____2690 in
                       mk uu____2689 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2738 = closures_as_binders_delayed cfg env bs in
                  (match uu____2738 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2780 =
                    let uu____2791 =
                      let uu____2798 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2798] in
                    closures_as_binders_delayed cfg env uu____2791 in
                  (match uu____2780 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2816 =
                         let uu____2817 =
                           let uu____2824 =
                             let uu____2825 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2825
                               FStar_Pervasives_Native.fst in
                           (uu____2824, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2817 in
                       mk uu____2816 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2916 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2916
                    | FStar_Util.Inr c ->
                        let uu____2930 = close_comp cfg env c in
                        FStar_Util.Inr uu____2930 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2946 =
                    let uu____2947 =
                      let uu____2974 = closure_as_term_delayed cfg env t11 in
                      (uu____2974, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2947 in
                  mk uu____2946 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3025 =
                    let uu____3026 =
                      let uu____3033 = closure_as_term_delayed cfg env t' in
                      let uu____3036 =
                        let uu____3037 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____3037 in
                      (uu____3033, uu____3036) in
                    FStar_Syntax_Syntax.Tm_meta uu____3026 in
                  mk uu____3025 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3097 =
                    let uu____3098 =
                      let uu____3105 = closure_as_term_delayed cfg env t' in
                      let uu____3108 =
                        let uu____3109 =
                          let uu____3116 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____3116) in
                        FStar_Syntax_Syntax.Meta_monadic uu____3109 in
                      (uu____3105, uu____3108) in
                    FStar_Syntax_Syntax.Tm_meta uu____3098 in
                  mk uu____3097 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3135 =
                    let uu____3136 =
                      let uu____3143 = closure_as_term_delayed cfg env t' in
                      let uu____3146 =
                        let uu____3147 =
                          let uu____3156 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____3156) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3147 in
                      (uu____3143, uu____3146) in
                    FStar_Syntax_Syntax.Tm_meta uu____3136 in
                  mk uu____3135 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3169 =
                    let uu____3170 =
                      let uu____3177 = closure_as_term_delayed cfg env t' in
                      (uu____3177, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____3170 in
                  mk uu____3169 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3217  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3236 =
                    let uu____3247 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3247
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3266 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___191_3278 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___191_3278.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___191_3278.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3266)) in
                  (match uu____3236 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___192_3294 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___192_3294.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___192_3294.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3305,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3364  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3389 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3389
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3409  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3431 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3431
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___193_3443 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___193_3443.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___193_3443.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___194_3444 = lb in
                    let uu____3445 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___194_3444.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___194_3444.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3445
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3475  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3564 =
                    match uu____3564 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3619 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3640 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3700  ->
                                        fun uu____3701  ->
                                          match (uu____3700, uu____3701) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3792 =
                                                norm_pat env3 p1 in
                                              (match uu____3792 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3640 with
                               | (pats1,env3) ->
                                   ((let uu___195_3874 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___195_3874.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___196_3893 = x in
                                let uu____3894 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___196_3893.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___196_3893.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3894
                                } in
                              ((let uu___197_3908 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___197_3908.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___198_3919 = x in
                                let uu____3920 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___198_3919.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___198_3919.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3920
                                } in
                              ((let uu___199_3934 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___199_3934.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___200_3950 = x in
                                let uu____3951 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___200_3950.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___200_3950.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3951
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___201_3958 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___201_3958.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3961 = norm_pat env1 pat in
                        (match uu____3961 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3990 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3990 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3996 =
                    let uu____3997 =
                      let uu____4020 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____4020) in
                    FStar_Syntax_Syntax.Tm_match uu____3997 in
                  mk uu____3996 t1.FStar_Syntax_Syntax.pos))
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
        | uu____4106 -> closure_as_term cfg env t
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
        | uu____4132 ->
            FStar_List.map
              (fun uu____4149  ->
                 match uu____4149 with
                 | (x,imp) ->
                     let uu____4168 = closure_as_term_delayed cfg env x in
                     (uu____4168, imp)) args
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
        let uu____4182 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4231  ->
                  fun uu____4232  ->
                    match (uu____4231, uu____4232) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___202_4302 = b in
                          let uu____4303 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___202_4302.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___202_4302.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4303
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____4182 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4396 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4409 = closure_as_term_delayed cfg env t in
                 let uu____4410 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4409 uu____4410
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4423 = closure_as_term_delayed cfg env t in
                 let uu____4424 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4423 uu____4424
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
                        (fun uu___172_4450  ->
                           match uu___172_4450 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4454 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4454
                           | f -> f)) in
                 let uu____4458 =
                   let uu___203_4459 = c1 in
                   let uu____4460 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4460;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___203_4459.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4458)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___173_4470  ->
            match uu___173_4470 with
            | FStar_Syntax_Syntax.DECREASES uu____4471 -> false
            | uu____4474 -> true))
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
                   (fun uu___174_4492  ->
                      match uu___174_4492 with
                      | FStar_Syntax_Syntax.DECREASES uu____4493 -> false
                      | uu____4496 -> true)) in
            let rc1 =
              let uu___204_4498 = rc in
              let uu____4499 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___204_4498.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4499;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4506 -> lopt
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
    let uu____4594 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4594 in
  let arg_as_bounded_int uu____4622 =
    match uu____4622 with
    | (a,uu____4634) ->
        let uu____4641 =
          let uu____4642 = FStar_Syntax_Subst.compress a in
          uu____4642.FStar_Syntax_Syntax.n in
        (match uu____4641 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4652;
                FStar_Syntax_Syntax.vars = uu____4653;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4655;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4656;_},uu____4657)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4696 =
               let uu____4701 = FStar_Util.int_of_string i in
               (fv1, uu____4701) in
             FStar_Pervasives_Native.Some uu____4696
         | uu____4706 -> FStar_Pervasives_Native.None) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4748 = f a in FStar_Pervasives_Native.Some uu____4748
    | uu____4749 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4799 = f a0 a1 in FStar_Pervasives_Native.Some uu____4799
    | uu____4800 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____4849 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4849 in
  let binary_op as_a f res args =
    let uu____4905 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4905 in
  let as_primitive_step uu____4929 =
    match uu____4929 with
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
           let uu____4977 = f x in
           FStar_Syntax_Embeddings.embed_int r uu____4977) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5005 = f x y in
             FStar_Syntax_Embeddings.embed_int r uu____5005) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____5026 = f x in
           FStar_Syntax_Embeddings.embed_bool r uu____5026) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5054 = f x y in
             FStar_Syntax_Embeddings.embed_bool r uu____5054) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____5082 = f x y in
             FStar_Syntax_Embeddings.embed_string r uu____5082) in
  let list_of_string' rng s =
    let name l =
      let uu____5096 =
        let uu____5097 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5097 in
      mk uu____5096 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5107 =
      let uu____5110 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5110 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5107 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    FStar_Syntax_Embeddings.embed_int rng r in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5157 = arg_as_string a1 in
        (match uu____5157 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5163 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2 in
             (match uu____5163 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5176 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____5176
              | uu____5177 -> FStar_Pervasives_Native.None)
         | uu____5182 -> FStar_Pervasives_Native.None)
    | uu____5185 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5195 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____5195 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5211 = FStar_Util.string_of_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____5211 in
  let string_of_bool2 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5241 args =
    match args with
    | uu____5253::(t,uu____5255)::[] ->
        let uu____5284 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5284
    | uu____5289 -> FStar_Pervasives_Native.None in
  let set_range_of1 uu____5311 args =
    match args with
    | uu____5321::(t,uu____5323)::(r,uu____5325)::[] ->
        let uu____5346 = FStar_Syntax_Embeddings.unembed_range_safe r in
        FStar_Util.bind_opt uu____5346
          (fun r1  ->
             FStar_Pervasives_Native.Some
               (let uu___205_5356 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___205_5356.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars =
                    (uu___205_5356.FStar_Syntax_Syntax.vars)
                }))
    | uu____5357 -> FStar_Pervasives_Native.None in
  let mk_range1 uu____5373 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5384 =
          let uu____5405 = arg_as_string fn in
          let uu____5408 = arg_as_int from_line in
          let uu____5411 = arg_as_int from_col in
          let uu____5414 = arg_as_int to_line in
          let uu____5417 = arg_as_int to_col in
          (uu____5405, uu____5408, uu____5411, uu____5414, uu____5417) in
        (match uu____5384 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5448 = FStar_Range.mk_pos from_l from_c in
               let uu____5449 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5448 uu____5449 in
             let uu____5450 = term_of_range r in
             FStar_Pervasives_Native.Some uu____5450
         | uu____5455 -> FStar_Pervasives_Native.None)
    | uu____5476 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5503)::(a1,uu____5505)::(a2,uu____5507)::[] ->
        let uu____5544 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5544 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5557 -> FStar_Pervasives_Native.None)
    | uu____5558 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5576 =
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
                                              let uu____5889 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5889,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5896 =
                                              let uu____5911 =
                                                let uu____5924 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5924,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list')) in
                                              let uu____5933 =
                                                let uu____5948 =
                                                  let uu____5963 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5963,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5972 =
                                                  let uu____5989 =
                                                    let uu____6010 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6010,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6025 =
                                                    let uu____6048 =
                                                      let uu____6067 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6067,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6080 =
                                                      let uu____6101 =
                                                        let uu____6116 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6116,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6101] in
                                                    uu____6048 :: uu____6080 in
                                                  uu____5989 :: uu____6025 in
                                                uu____5948 :: uu____5972 in
                                              uu____5911 :: uu____5933 in
                                            uu____5876 :: uu____5896 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5861 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5846 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5831 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5816 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5801 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5786 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5771 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5756 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5741 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5726 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5711 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                FStar_Syntax_Embeddings.embed_bool r (x >= y))))
                      :: uu____5696 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              FStar_Syntax_Embeddings.embed_bool r (x > y))))
                    :: uu____5681 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            FStar_Syntax_Embeddings.embed_bool r (x <= y))))
                  :: uu____5666 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          FStar_Syntax_Embeddings.embed_bool r (x < y))))
                :: uu____5651 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5636 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5621 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5606 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5591 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5576 in
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
      let uu____6705 =
        let uu____6706 =
          let uu____6707 = FStar_Syntax_Syntax.as_arg c in [uu____6707] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6706 in
      uu____6705 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6742 =
              let uu____6755 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6755, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6774  ->
                        fun uu____6775  ->
                          match (uu____6774, uu____6775) with
                          | ((int_to_t1,x),(uu____6794,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6804 =
              let uu____6819 =
                let uu____6832 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6832, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6851  ->
                          fun uu____6852  ->
                            match (uu____6851, uu____6852) with
                            | ((int_to_t1,x),(uu____6871,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6881 =
                let uu____6896 =
                  let uu____6909 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6909, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6928  ->
                            fun uu____6929  ->
                              match (uu____6928, uu____6929) with
                              | ((int_to_t1,x),(uu____6948,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6896] in
              uu____6819 :: uu____6881 in
            uu____6742 :: uu____6804)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____7047)::(a1,uu____7049)::(a2,uu____7051)::[] ->
        let uu____7088 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7088 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___206_7094 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___206_7094.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___206_7094.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___207_7098 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___207_7098.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___207_7098.FStar_Syntax_Syntax.vars)
                })
         | uu____7099 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7101)::uu____7102::(a1,uu____7104)::(a2,uu____7106)::[] ->
        let uu____7155 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7155 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___206_7161 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___206_7161.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___206_7161.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___207_7165 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___207_7165.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___207_7165.FStar_Syntax_Syntax.vars)
                })
         | uu____7166 -> FStar_Pervasives_Native.None)
    | uu____7167 -> failwith "Unexpected number of arguments" in
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
let mk_psc_subst:
  'Auu____7178 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7178) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7238  ->
           fun subst1  ->
             match uu____7238 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____7280)) ->
                      let uu____7339 = b in
                      (match uu____7339 with
                       | (bv,uu____7347) ->
                           let uu____7348 =
                             let uu____7349 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7349 in
                           if uu____7348
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let x =
                                let uu____7355 =
                                  FStar_Syntax_Util.un_alien term1 in
                                FStar_All.pipe_right uu____7355
                                  FStar_Dyn.undyn in
                              let b1 =
                                let uu____7357 =
                                  let uu___208_7358 = bv in
                                  let uu____7359 =
                                    FStar_Syntax_Subst.subst subst1
                                      (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___208_7358.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___208_7358.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____7359
                                  } in
                                FStar_Syntax_Syntax.freshen_bv uu____7357 in
                              let b_for_x =
                                let uu____7363 =
                                  let uu____7370 =
                                    FStar_Syntax_Syntax.bv_to_name b1 in
                                  ((FStar_Pervasives_Native.fst x),
                                    uu____7370) in
                                FStar_Syntax_Syntax.NT uu____7363 in
                              let subst2 =
                                FStar_List.filter
                                  (fun uu___175_7379  ->
                                     match uu___175_7379 with
                                     | FStar_Syntax_Syntax.NT
                                         (uu____7380,{
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_name
                                                         b';
                                                       FStar_Syntax_Syntax.pos
                                                         = uu____7382;
                                                       FStar_Syntax_Syntax.vars
                                                         = uu____7383;_})
                                         ->
                                         Prims.op_Negation
                                           (FStar_Ident.ident_equals
                                              b1.FStar_Syntax_Syntax.ppname
                                              b'.FStar_Syntax_Syntax.ppname)
                                     | uu____7388 -> true) subst1 in
                              b_for_x :: subst2))
                  | uu____7389 -> subst1)) env []
let reduce_primops:
  'Auu____7412 'Auu____7413 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7413) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7412 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____7454 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7454
          then tm
          else
            (let uu____7456 = FStar_Syntax_Util.head_and_args tm in
             match uu____7456 with
             | (head1,args) ->
                 let uu____7493 =
                   let uu____7494 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7494.FStar_Syntax_Syntax.n in
                 (match uu____7493 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7498 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7498 with
                       | FStar_Pervasives_Native.None  -> tm
                       | FStar_Pervasives_Native.Some prim_step ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7515  ->
                                   let uu____7516 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7517 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7524 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7516 uu____7517 uu____7524);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7529  ->
                                   let uu____7530 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7530);
                              (let psc =
                                 let uu____7532 =
                                   if prim_step.requires_binder_substitution
                                   then mk_psc_subst cfg env
                                   else [] in
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst = uu____7532
                                 } in
                               let uu____7534 =
                                 prim_step.interpretation psc args in
                               match uu____7534 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7540  ->
                                         let uu____7541 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7541);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7547  ->
                                         let uu____7548 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7549 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7548 uu____7549);
                                    reduced))))
                  | uu____7550 -> tm))
let reduce_equality:
  'Auu____7561 'Auu____7562 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7562) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7561 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___209_7600 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___209_7600.tcenv);
           delta_level = (uu___209_7600.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  'Auu____7613 'Auu____7614 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7614) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7613 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7656 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7656
          then tm1
          else
            (let w t =
               let uu___210_7668 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___210_7668.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___210_7668.FStar_Syntax_Syntax.vars)
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
               | uu____7685 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7725;
                         FStar_Syntax_Syntax.vars = uu____7726;_},uu____7727);
                    FStar_Syntax_Syntax.pos = uu____7728;
                    FStar_Syntax_Syntax.vars = uu____7729;_},args)
                 ->
                 let uu____7755 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7755
                 then
                   let uu____7756 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7756 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7811)::
                        (uu____7812,(arg,uu____7814))::[] -> arg
                    | (uu____7879,(arg,uu____7881))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7882)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7947)::uu____7948::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8011::(FStar_Pervasives_Native.Some (false
                                   ),uu____8012)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8075 -> tm1)
                 else
                   (let uu____8091 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8091
                    then
                      let uu____8092 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8092 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8147)::uu____8148::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8211::(FStar_Pervasives_Native.Some (true
                                     ),uu____8212)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8275)::
                          (uu____8276,(arg,uu____8278))::[] -> arg
                      | (uu____8343,(arg,uu____8345))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8346)::[]
                          -> arg
                      | uu____8411 -> tm1
                    else
                      (let uu____8427 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8427
                       then
                         let uu____8428 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8428 with
                         | uu____8483::(FStar_Pervasives_Native.Some (true
                                        ),uu____8484)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8547)::uu____8548::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8611)::
                             (uu____8612,(arg,uu____8614))::[] -> arg
                         | (uu____8679,(p,uu____8681))::(uu____8682,(q,uu____8684))::[]
                             ->
                             let uu____8749 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8749
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____8751 -> tm1
                       else
                         (let uu____8767 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8767
                          then
                            let uu____8768 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8768 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8823)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8862)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8901 -> tm1
                          else
                            (let uu____8917 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8917
                             then
                               match args with
                               | (t,uu____8919)::[] ->
                                   let uu____8936 =
                                     let uu____8937 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8937.FStar_Syntax_Syntax.n in
                                   (match uu____8936 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8940::[],body,uu____8942) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8969 -> tm1)
                                    | uu____8972 -> tm1)
                               | (uu____8973,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8974))::
                                   (t,uu____8976)::[] ->
                                   let uu____9015 =
                                     let uu____9016 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9016.FStar_Syntax_Syntax.n in
                                   (match uu____9015 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9019::[],body,uu____9021) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9048 -> tm1)
                                    | uu____9051 -> tm1)
                               | uu____9052 -> tm1
                             else
                               (let uu____9062 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9062
                                then
                                  match args with
                                  | (t,uu____9064)::[] ->
                                      let uu____9081 =
                                        let uu____9082 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9082.FStar_Syntax_Syntax.n in
                                      (match uu____9081 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9085::[],body,uu____9087)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9114 -> tm1)
                                       | uu____9117 -> tm1)
                                  | (uu____9118,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9119))::(t,uu____9121)::[] ->
                                      let uu____9160 =
                                        let uu____9161 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9161.FStar_Syntax_Syntax.n in
                                      (match uu____9160 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9164::[],body,uu____9166)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9193 -> tm1)
                                       | uu____9196 -> tm1)
                                  | uu____9197 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9208;
                    FStar_Syntax_Syntax.vars = uu____9209;_},args)
                 ->
                 let uu____9231 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9231
                 then
                   let uu____9232 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9232 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9287)::
                        (uu____9288,(arg,uu____9290))::[] -> arg
                    | (uu____9355,(arg,uu____9357))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9358)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9423)::uu____9424::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9487::(FStar_Pervasives_Native.Some (false
                                   ),uu____9488)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9551 -> tm1)
                 else
                   (let uu____9567 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9567
                    then
                      let uu____9568 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9568 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9623)::uu____9624::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9687::(FStar_Pervasives_Native.Some (true
                                     ),uu____9688)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9751)::
                          (uu____9752,(arg,uu____9754))::[] -> arg
                      | (uu____9819,(arg,uu____9821))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9822)::[]
                          -> arg
                      | uu____9887 -> tm1
                    else
                      (let uu____9903 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9903
                       then
                         let uu____9904 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9904 with
                         | uu____9959::(FStar_Pervasives_Native.Some (true
                                        ),uu____9960)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10023)::uu____10024::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10087)::
                             (uu____10088,(arg,uu____10090))::[] -> arg
                         | (uu____10155,(p,uu____10157))::(uu____10158,
                                                           (q,uu____10160))::[]
                             ->
                             let uu____10225 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10225
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____10227 -> tm1
                       else
                         (let uu____10243 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10243
                          then
                            let uu____10244 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10244 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10299)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10338)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10377 -> tm1
                          else
                            (let uu____10393 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10393
                             then
                               match args with
                               | (t,uu____10395)::[] ->
                                   let uu____10412 =
                                     let uu____10413 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10413.FStar_Syntax_Syntax.n in
                                   (match uu____10412 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10416::[],body,uu____10418) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10445 -> tm1)
                                    | uu____10448 -> tm1)
                               | (uu____10449,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10450))::
                                   (t,uu____10452)::[] ->
                                   let uu____10491 =
                                     let uu____10492 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10492.FStar_Syntax_Syntax.n in
                                   (match uu____10491 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10495::[],body,uu____10497) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10524 -> tm1)
                                    | uu____10527 -> tm1)
                               | uu____10528 -> tm1
                             else
                               (let uu____10538 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10538
                                then
                                  match args with
                                  | (t,uu____10540)::[] ->
                                      let uu____10557 =
                                        let uu____10558 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10558.FStar_Syntax_Syntax.n in
                                      (match uu____10557 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10561::[],body,uu____10563)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10590 -> tm1)
                                       | uu____10593 -> tm1)
                                  | (uu____10594,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10595))::(t,uu____10597)::[] ->
                                      let uu____10636 =
                                        let uu____10637 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10637.FStar_Syntax_Syntax.n in
                                      (match uu____10636 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10640::[],body,uu____10642)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10669 -> tm1)
                                       | uu____10672 -> tm1)
                                  | uu____10673 -> tm1
                                else reduce_equality cfg env stack1 tm1)))))
             | uu____10683 -> tm1)
let is_norm_request:
  'Auu____10690 .
    FStar_Syntax_Syntax.term -> 'Auu____10690 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10703 =
        let uu____10710 =
          let uu____10711 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10711.FStar_Syntax_Syntax.n in
        (uu____10710, args) in
      match uu____10703 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10717::uu____10718::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10722::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10727::uu____10728::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10731 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___176_10743  ->
    match uu___176_10743 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10749 =
          let uu____10752 =
            let uu____10753 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10753 in
          [uu____10752] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10749
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10772 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10772) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10810 =
          let uu____10813 =
            let uu____10818 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10818 s in
          FStar_All.pipe_right uu____10813 FStar_Util.must in
        FStar_All.pipe_right uu____10810 tr_norm_steps in
      match args with
      | uu____10843::(tm,uu____10845)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10868)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10883)::uu____10884::(tm,uu____10886)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10926 =
              let uu____10929 = full_norm steps in parse_steps uu____10929 in
            Beta :: uu____10926 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10938 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___177_10956  ->
    match uu___177_10956 with
    | (App
        (uu____10959,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10960;
                       FStar_Syntax_Syntax.vars = uu____10961;_},uu____10962,uu____10963))::uu____10964
        -> true
    | uu____10971 -> false
let firstn:
  'Auu____10980 .
    Prims.int ->
      'Auu____10980 Prims.list ->
        ('Auu____10980 Prims.list,'Auu____10980 Prims.list)
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
          (uu____11018,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11019;
                         FStar_Syntax_Syntax.vars = uu____11020;_},uu____11021,uu____11022))::uu____11023
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11030 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11146  ->
               let uu____11147 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11148 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11149 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11156 =
                 let uu____11157 =
                   let uu____11160 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11160 in
                 stack_to_string uu____11157 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11147 uu____11148 uu____11149 uu____11156);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11183 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11208 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11225 =
                 let uu____11226 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11227 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11226 uu____11227 in
               failwith uu____11225
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11228 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____11245 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____11246 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11247;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11248;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11251;
                 FStar_Syntax_Syntax.fv_delta = uu____11252;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11253;
                 FStar_Syntax_Syntax.fv_delta = uu____11254;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11255);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11263 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11263 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____11269  ->
                     let uu____11270 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11271 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11270 uu____11271);
                if b
                then
                  (let uu____11272 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____11272 t1 fv)
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
                 let uu___211_11311 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___211_11311.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___211_11311.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11344 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11344) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___212_11352 = cfg in
                 let uu____11353 =
                   FStar_List.filter
                     (fun uu___178_11356  ->
                        match uu___178_11356 with
                        | UnfoldOnly uu____11357 -> false
                        | NoDeltaSteps  -> false
                        | uu____11360 -> true) cfg.steps in
                 {
                   steps = uu____11353;
                   tcenv = (uu___212_11352.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___212_11352.primitive_steps)
                 } in
               let uu____11361 = get_norm_request (norm cfg' env []) args in
               (match uu____11361 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11377 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___179_11382  ->
                                match uu___179_11382 with
                                | UnfoldUntil uu____11383 -> true
                                | UnfoldOnly uu____11384 -> true
                                | uu____11387 -> false)) in
                      if uu____11377
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___213_11392 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___213_11392.tcenv);
                        delta_level;
                        primitive_steps = (uu___213_11392.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11403 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11403
                      then
                        let uu____11406 =
                          let uu____11407 =
                            let uu____11412 = FStar_Util.now () in
                            (t1, uu____11412) in
                          Debug uu____11407 in
                        uu____11406 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11414;
                  FStar_Syntax_Syntax.vars = uu____11415;_},a1::a2::rest)
               ->
               let uu____11463 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11463 with
                | (hd1,uu____11479) ->
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
                    (FStar_Const.Const_reflect uu____11544);
                  FStar_Syntax_Syntax.pos = uu____11545;
                  FStar_Syntax_Syntax.vars = uu____11546;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11578 = FStar_List.tl stack1 in
               norm cfg env uu____11578 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11581;
                  FStar_Syntax_Syntax.vars = uu____11582;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11614 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11614 with
                | (reify_head,uu____11630) ->
                    let a1 =
                      let uu____11652 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11652 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11655);
                            FStar_Syntax_Syntax.pos = uu____11656;
                            FStar_Syntax_Syntax.vars = uu____11657;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11691 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11701 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11701
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11708 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11708
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11711 =
                      let uu____11718 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11718, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11711 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___180_11731  ->
                         match uu___180_11731 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11734 =
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
                 if uu____11734
                 then false
                 else
                   (let uu____11736 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___181_11743  ->
                              match uu___181_11743 with
                              | UnfoldOnly uu____11744 -> true
                              | uu____11747 -> false)) in
                    match uu____11736 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11751 -> should_delta) in
               (log cfg
                  (fun uu____11759  ->
                     let uu____11760 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11761 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11762 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11760 uu____11761 uu____11762);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11765 = lookup_bvar env x in
               (match uu____11765 with
                | Univ uu____11768 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11817 = FStar_ST.op_Bang r in
                      (match uu____11817 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11954  ->
                                 let uu____11955 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11956 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11955
                                   uu____11956);
                            (let uu____11957 =
                               let uu____11958 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11958.FStar_Syntax_Syntax.n in
                             match uu____11957 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11961 ->
                                 norm cfg env2 stack1 t'
                             | uu____11978 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____12036)::uu____12037 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12046)::uu____12047 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12057,uu____12058))::stack_rest ->
                    (match c with
                     | Univ uu____12062 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12071 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12092  ->
                                    let uu____12093 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12093);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12133  ->
                                    let uu____12134 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12134);
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
                      (let uu___214_12184 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___214_12184.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12269  ->
                          let uu____12270 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12270);
                     norm cfg env stack2 t1)
                | (Debug uu____12271)::uu____12272 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12279 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12279
                    else
                      (let uu____12281 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12281 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12323  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12351 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12351
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12361 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12361)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_12366 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_12366.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_12366.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12367 -> lopt in
                           (log cfg
                              (fun uu____12373  ->
                                 let uu____12374 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12374);
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
                | (Meta uu____12397)::uu____12398 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12405 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12405
                    else
                      (let uu____12407 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12407 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12449  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12477 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12477
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12487 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12487)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_12492 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_12492.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_12492.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12493 -> lopt in
                           (log cfg
                              (fun uu____12499  ->
                                 let uu____12500 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12500);
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
                | (Let uu____12523)::uu____12524 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12535 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12535
                    else
                      (let uu____12537 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12537 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12579  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12607 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12607
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12617 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12617)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_12622 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_12622.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_12622.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12623 -> lopt in
                           (log cfg
                              (fun uu____12629  ->
                                 let uu____12630 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12630);
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
                | (App uu____12653)::uu____12654 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12665 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12665
                    else
                      (let uu____12667 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12667 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12709  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12737 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12737
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12747 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12747)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_12752 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_12752.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_12752.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12753 -> lopt in
                           (log cfg
                              (fun uu____12759  ->
                                 let uu____12760 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12760);
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
                | (Abs uu____12783)::uu____12784 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12799 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12799
                    else
                      (let uu____12801 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12801 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12843  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12871 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12871
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12881 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12881)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_12886 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_12886.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_12886.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12887 -> lopt in
                           (log cfg
                              (fun uu____12893  ->
                                 let uu____12894 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12894);
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
                      let uu____12917 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12917
                    else
                      (let uu____12919 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12919 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12961  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12989 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12989
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12999 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12999)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_13004 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_13004.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_13004.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13005 -> lopt in
                           (log cfg
                              (fun uu____13011  ->
                                 let uu____13012 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13012);
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
                      (fun uu____13073  ->
                         fun stack2  ->
                           match uu____13073 with
                           | (a,aq) ->
                               let uu____13085 =
                                 let uu____13086 =
                                   let uu____13093 =
                                     let uu____13094 =
                                       let uu____13125 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13125, false) in
                                     Clos uu____13094 in
                                   (uu____13093, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13086 in
                               uu____13085 :: stack2) args) in
               (log cfg
                  (fun uu____13201  ->
                     let uu____13202 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13202);
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
                             ((let uu___216_13238 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___216_13238.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___216_13238.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____13239 ->
                      let uu____13244 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13244)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13247 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13247 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13278 =
                          let uu____13279 =
                            let uu____13286 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___217_13288 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___217_13288.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___217_13288.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13286) in
                          FStar_Syntax_Syntax.Tm_refine uu____13279 in
                        mk uu____13278 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13307 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____13307
               else
                 (let uu____13309 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13309 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13317 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13341  -> dummy :: env1) env) in
                        norm_comp cfg uu____13317 c1 in
                      let t2 =
                        let uu____13363 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13363 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13422)::uu____13423 ->
                    (log cfg
                       (fun uu____13434  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (Arg uu____13435)::uu____13436 ->
                    (log cfg
                       (fun uu____13447  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (App
                    (uu____13448,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13449;
                                   FStar_Syntax_Syntax.vars = uu____13450;_},uu____13451,uu____13452))::uu____13453
                    ->
                    (log cfg
                       (fun uu____13462  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | (MemoLazy uu____13463)::uu____13464 ->
                    (log cfg
                       (fun uu____13475  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack1 t11)
                | uu____13476 ->
                    (log cfg
                       (fun uu____13479  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13483  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13500 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13500
                         | FStar_Util.Inr c ->
                             let uu____13508 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13508 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       let uu____13514 =
                         let uu____13515 =
                           let uu____13516 =
                             let uu____13543 =
                               FStar_Syntax_Util.unascribe t12 in
                             (uu____13543, (tc1, tacopt1), l) in
                           FStar_Syntax_Syntax.Tm_ascribed uu____13516 in
                         mk uu____13515 t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env stack1 uu____13514))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13619,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13620;
                               FStar_Syntax_Syntax.lbunivs = uu____13621;
                               FStar_Syntax_Syntax.lbtyp = uu____13622;
                               FStar_Syntax_Syntax.lbeff = uu____13623;
                               FStar_Syntax_Syntax.lbdef = uu____13624;_}::uu____13625),uu____13626)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13662 =
                 (let uu____13665 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13665) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13667 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13667))) in
               if uu____13662
               then
                 let binder =
                   let uu____13669 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13669 in
                 let env1 =
                   let uu____13679 =
                     let uu____13686 =
                       let uu____13687 =
                         let uu____13718 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13718,
                           false) in
                       Clos uu____13687 in
                     ((FStar_Pervasives_Native.Some binder), uu____13686) in
                   uu____13679 :: env in
                 (log cfg
                    (fun uu____13803  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack1 body)
               else
                 (let uu____13805 =
                    let uu____13810 =
                      let uu____13811 =
                        let uu____13812 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13812
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13811] in
                    FStar_Syntax_Subst.open_term uu____13810 body in
                  match uu____13805 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13821  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13829 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13829 in
                          FStar_Util.Inl
                            (let uu___218_13839 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___218_13839.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___218_13839.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13842  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___219_13844 = lb in
                           let uu____13845 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___219_13844.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___219_13844.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13845
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13880  -> dummy :: env1) env) in
                         let cfg1 = only_strong_steps cfg in
                         log cfg1
                           (fun uu____13902  ->
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
               let uu____13919 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13919 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13955 =
                               let uu___220_13956 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___220_13956.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___220_13956.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13955 in
                           let uu____13957 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13957 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13983 =
                                   FStar_List.map (fun uu____13999  -> dummy)
                                     lbs1 in
                                 let uu____14000 =
                                   let uu____14009 =
                                     FStar_List.map
                                       (fun uu____14029  -> dummy) xs1 in
                                   FStar_List.append uu____14009 env in
                                 FStar_List.append uu____13983 uu____14000 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14053 =
                                       let uu___221_14054 = rc in
                                       let uu____14055 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___221_14054.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14055;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___221_14054.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14053
                                 | uu____14062 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___222_14066 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___222_14066.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___222_14066.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14076 =
                        FStar_List.map (fun uu____14092  -> dummy) lbs2 in
                      FStar_List.append uu____14076 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14100 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14100 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___223_14116 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___223_14116.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___223_14116.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14143 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____14143
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14162 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14238  ->
                        match uu____14238 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___224_14359 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___224_14359.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___224_14359.FStar_Syntax_Syntax.sort)
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
               (match uu____14162 with
                | (rec_env,memos,uu____14556) ->
                    let uu____14609 =
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
                             let uu____15140 =
                               let uu____15147 =
                                 let uu____15148 =
                                   let uu____15179 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15179, false) in
                                 Clos uu____15148 in
                               (FStar_Pervasives_Native.None, uu____15147) in
                             uu____15140 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15284 =
                      let uu____15285 = should_reify cfg stack1 in
                      Prims.op_Negation uu____15285 in
                    if uu____15284
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____15295 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15295
                        then
                          let uu___225_15296 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___225_15296.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___225_15296.primitive_steps)
                          }
                        else
                          (let uu___226_15298 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___226_15298.tcenv);
                             delta_level = (uu___226_15298.delta_level);
                             primitive_steps =
                               (uu___226_15298.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____15300 =
                         let uu____15301 = FStar_Syntax_Subst.compress head1 in
                         uu____15301.FStar_Syntax_Syntax.n in
                       match uu____15300 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15319 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15319 with
                            | (uu____15320,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15326 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15334 =
                                         let uu____15335 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15335.FStar_Syntax_Syntax.n in
                                       match uu____15334 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15341,uu____15342))
                                           ->
                                           let uu____15351 =
                                             let uu____15352 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15352.FStar_Syntax_Syntax.n in
                                           (match uu____15351 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15358,msrc,uu____15360))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15369 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15369
                                            | uu____15370 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15371 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15372 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15372 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___227_15377 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___227_15377.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___227_15377.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___227_15377.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15378 =
                                            FStar_List.tl stack1 in
                                          let uu____15379 =
                                            let uu____15380 =
                                              let uu____15383 =
                                                let uu____15384 =
                                                  let uu____15397 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15397) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15384 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15383 in
                                            uu____15380
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15378
                                            uu____15379
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15413 =
                                            let uu____15414 = is_return body in
                                            match uu____15414 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15418;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15419;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15424 -> false in
                                          if uu____15413
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
                                               let uu____15448 =
                                                 let uu____15451 =
                                                   let uu____15452 =
                                                     let uu____15469 =
                                                       let uu____15472 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15472] in
                                                     (uu____15469, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15452 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15451 in
                                               uu____15448
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15488 =
                                                 let uu____15489 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15489.FStar_Syntax_Syntax.n in
                                               match uu____15488 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15495::uu____15496::[])
                                                   ->
                                                   let uu____15503 =
                                                     let uu____15506 =
                                                       let uu____15507 =
                                                         let uu____15514 =
                                                           let uu____15517 =
                                                             let uu____15518
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15518 in
                                                           let uu____15519 =
                                                             let uu____15522
                                                               =
                                                               let uu____15523
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15523 in
                                                             [uu____15522] in
                                                           uu____15517 ::
                                                             uu____15519 in
                                                         (bind1, uu____15514) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15507 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15506 in
                                                   uu____15503
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15531 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15537 =
                                                 let uu____15540 =
                                                   let uu____15541 =
                                                     let uu____15556 =
                                                       let uu____15559 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15560 =
                                                         let uu____15563 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15564 =
                                                           let uu____15567 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15568 =
                                                             let uu____15571
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15572
                                                               =
                                                               let uu____15575
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15576
                                                                 =
                                                                 let uu____15579
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15579] in
                                                               uu____15575 ::
                                                                 uu____15576 in
                                                             uu____15571 ::
                                                               uu____15572 in
                                                           uu____15567 ::
                                                             uu____15568 in
                                                         uu____15563 ::
                                                           uu____15564 in
                                                       uu____15559 ::
                                                         uu____15560 in
                                                     (bind_inst, uu____15556) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15541 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15540 in
                                               uu____15537
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15587 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15587 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15611 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15611 with
                            | (uu____15612,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15647 =
                                        let uu____15648 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____15648.FStar_Syntax_Syntax.n in
                                      match uu____15647 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15654) -> t4
                                      | uu____15659 -> head2 in
                                    let uu____15660 =
                                      let uu____15661 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____15661.FStar_Syntax_Syntax.n in
                                    match uu____15660 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15667 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____15668 = maybe_extract_fv head2 in
                                  match uu____15668 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15678 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15678
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____15683 =
                                          maybe_extract_fv head3 in
                                        match uu____15683 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15688 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15689 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____15694 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____15709 =
                                    match uu____15709 with
                                    | (e,q) ->
                                        let uu____15716 =
                                          let uu____15717 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____15717.FStar_Syntax_Syntax.n in
                                        (match uu____15716 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15732 -> false) in
                                  let uu____15733 =
                                    let uu____15734 =
                                      let uu____15741 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____15741 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15734 in
                                  if uu____15733
                                  then
                                    let uu____15746 =
                                      let uu____15747 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15747 in
                                    failwith uu____15746
                                  else ());
                                 (let uu____15749 =
                                    maybe_unfold_action head_app in
                                  match uu____15749 with
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
                                      let uu____15788 = FStar_List.tl stack1 in
                                      norm cfg env uu____15788 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15802 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____15802 in
                           let uu____15803 = FStar_List.tl stack1 in
                           norm cfg env uu____15803 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____15924  ->
                                     match uu____15924 with
                                     | (pat,wopt,tm) ->
                                         let uu____15972 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____15972))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16004 = FStar_List.tl stack1 in
                           norm cfg env uu____16004 tm
                       | uu____16005 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16013 = should_reify cfg stack1 in
                    if uu____16013
                    then
                      let uu____16014 = FStar_List.tl stack1 in
                      let uu____16015 =
                        let uu____16016 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16016 in
                      norm cfg env uu____16014 uu____16015
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16019 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16019
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___228_16028 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___228_16028.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___228_16028.primitive_steps)
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
                | uu____16030 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____16032::uu____16033 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16038) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16039 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____16070 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16084 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16084
                             | uu____16095 -> m in
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
              let uu____16107 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16107 in
            let uu____16108 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16108 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16121  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16132  ->
                      let uu____16133 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16134 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16133
                        uu____16134);
                 (let t1 =
                    let uu____16136 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16136
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
                    | (UnivArgs (us',uu____16146))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____16201 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____16204 ->
                        let uu____16207 =
                          let uu____16208 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16208 in
                        failwith uu____16207
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
              let uu____16218 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16218 with
              | (uu____16219,return_repr) ->
                  let return_inst =
                    let uu____16228 =
                      let uu____16229 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16229.FStar_Syntax_Syntax.n in
                    match uu____16228 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16235::[]) ->
                        let uu____16242 =
                          let uu____16245 =
                            let uu____16246 =
                              let uu____16253 =
                                let uu____16256 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16256] in
                              (return_tm, uu____16253) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16246 in
                          FStar_Syntax_Syntax.mk uu____16245 in
                        uu____16242 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16264 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16267 =
                    let uu____16270 =
                      let uu____16271 =
                        let uu____16286 =
                          let uu____16289 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16290 =
                            let uu____16293 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16293] in
                          uu____16289 :: uu____16290 in
                        (return_inst, uu____16286) in
                      FStar_Syntax_Syntax.Tm_app uu____16271 in
                    FStar_Syntax_Syntax.mk uu____16270 in
                  uu____16267 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16302 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16302 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16305 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16305
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16306;
                     FStar_TypeChecker_Env.mtarget = uu____16307;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16308;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16319;
                     FStar_TypeChecker_Env.mtarget = uu____16320;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16321;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16339 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16339)
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
                (fun uu____16395  ->
                   match uu____16395 with
                   | (a,imp) ->
                       let uu____16406 = norm cfg env [] a in
                       (uu____16406, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___229_16423 = comp1 in
            let uu____16426 =
              let uu____16427 =
                let uu____16436 = norm cfg env [] t in
                let uu____16437 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16436, uu____16437) in
              FStar_Syntax_Syntax.Total uu____16427 in
            {
              FStar_Syntax_Syntax.n = uu____16426;
              FStar_Syntax_Syntax.pos =
                (uu___229_16423.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___229_16423.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___230_16452 = comp1 in
            let uu____16455 =
              let uu____16456 =
                let uu____16465 = norm cfg env [] t in
                let uu____16466 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16465, uu____16466) in
              FStar_Syntax_Syntax.GTotal uu____16456 in
            {
              FStar_Syntax_Syntax.n = uu____16455;
              FStar_Syntax_Syntax.pos =
                (uu___230_16452.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___230_16452.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16518  ->
                      match uu____16518 with
                      | (a,i) ->
                          let uu____16529 = norm cfg env [] a in
                          (uu____16529, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___182_16540  ->
                      match uu___182_16540 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16544 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16544
                      | f -> f)) in
            let uu___231_16548 = comp1 in
            let uu____16551 =
              let uu____16552 =
                let uu___232_16553 = ct in
                let uu____16554 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16555 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16558 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16554;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___232_16553.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16555;
                  FStar_Syntax_Syntax.effect_args = uu____16558;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16552 in
            {
              FStar_Syntax_Syntax.n = uu____16551;
              FStar_Syntax_Syntax.pos =
                (uu___231_16548.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___231_16548.FStar_Syntax_Syntax.vars)
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
            (let uu___233_16576 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___233_16576.tcenv);
               delta_level = (uu___233_16576.delta_level);
               primitive_steps = (uu___233_16576.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____16581 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16581 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16584 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___234_16603 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___234_16603.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___234_16603.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16610 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16610
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
                    let uu___235_16621 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___235_16621.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___235_16621.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___235_16621.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___236_16623 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___236_16623.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___236_16623.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___236_16623.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___236_16623.FStar_Syntax_Syntax.flags)
                    } in
              let uu___237_16624 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___237_16624.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___237_16624.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____16626 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16629  ->
        match uu____16629 with
        | (x,imp) ->
            let uu____16632 =
              let uu___238_16633 = x in
              let uu____16634 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___238_16633.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___238_16633.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16634
              } in
            (uu____16632, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16640 =
          FStar_List.fold_left
            (fun uu____16658  ->
               fun b  ->
                 match uu____16658 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16640 with | (nbs,uu____16698) -> FStar_List.rev nbs
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
            let uu____16714 =
              let uu___239_16715 = rc in
              let uu____16716 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___239_16715.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16716;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___239_16715.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16714
        | uu____16723 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____16736  ->
               let uu____16737 = FStar_Syntax_Print.tag_of_term t in
               let uu____16738 = FStar_Syntax_Print.term_to_string t in
               let uu____16739 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16746 =
                 let uu____16747 =
                   let uu____16750 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16750 in
                 stack_to_string uu____16747 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16737 uu____16738 uu____16739 uu____16746);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____16779 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16779
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16781 =
                     let uu____16782 =
                       let uu____16783 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16783 in
                     FStar_Util.string_of_int uu____16782 in
                   let uu____16788 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16789 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16781 uu____16788 uu____16789
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___240_16807 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___240_16807.tcenv);
                    delta_level = dl;
                    primitive_steps = ps
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____16900  ->
                     let uu____16901 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16901);
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
               let uu____16937 =
                 let uu___241_16938 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___241_16938.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___241_16938.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____16937
           | (Arg (Univ uu____16939,uu____16940,uu____16941))::uu____16942 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16945,uu____16946))::uu____16947 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____16963),aq,r))::stack2 ->
               (log cfg
                  (fun uu____17016  ->
                     let uu____17017 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17017);
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
                  (let uu____17027 = FStar_ST.op_Bang m in
                   match uu____17027 with
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
                   | FStar_Pervasives_Native.Some (uu____17171,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17214 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____17214
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____17226  ->
                     let uu____17227 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17227);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17232 =
                   log cfg
                     (fun uu____17237  ->
                        let uu____17238 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17239 =
                          let uu____17240 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17257  ->
                                    match uu____17257 with
                                    | (p,uu____17267,uu____17268) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17240
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17238 uu____17239);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___183_17285  ->
                                match uu___183_17285 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17286 -> false)) in
                      let steps' =
                        let uu____17290 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____17290
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      only_strong_steps
                        (let uu___242_17296 = cfg in
                         {
                           steps = (FStar_List.append steps' cfg.steps);
                           tcenv = (uu___242_17296.tcenv);
                           delta_level = new_delta;
                           primitive_steps = (uu___242_17296.primitive_steps)
                         }) in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17328 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17349 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17409  ->
                                    fun uu____17410  ->
                                      match (uu____17409, uu____17410) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17501 = norm_pat env3 p1 in
                                          (match uu____17501 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17349 with
                           | (pats1,env3) ->
                               ((let uu___243_17583 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___243_17583.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___244_17602 = x in
                            let uu____17603 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___244_17602.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___244_17602.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17603
                            } in
                          ((let uu___245_17617 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___245_17617.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___246_17628 = x in
                            let uu____17629 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___246_17628.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___246_17628.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17629
                            } in
                          ((let uu___247_17643 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___247_17643.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___248_17659 = x in
                            let uu____17660 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___248_17659.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___248_17659.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17660
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___249_17667 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___249_17667.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17677 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17691 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17691 with
                                  | (p,wopt,e) ->
                                      let uu____17711 = norm_pat env1 p in
                                      (match uu____17711 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17736 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17736 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17742 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____17742) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17752) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17757 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17758;
                         FStar_Syntax_Syntax.fv_delta = uu____17759;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17760;
                         FStar_Syntax_Syntax.fv_delta = uu____17761;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17762);_}
                       -> true
                   | uu____17769 -> false in
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
                   let uu____17914 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17914 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18001 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____18040 ->
                                 let uu____18041 =
                                   let uu____18042 = is_cons head1 in
                                   Prims.op_Negation uu____18042 in
                                 FStar_Util.Inr uu____18041)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18067 =
                              let uu____18068 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18068.FStar_Syntax_Syntax.n in
                            (match uu____18067 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18086 ->
                                 let uu____18087 =
                                   let uu____18088 = is_cons head1 in
                                   Prims.op_Negation uu____18088 in
                                 FStar_Util.Inr uu____18087))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18157)::rest_a,(p1,uu____18160)::rest_p) ->
                       let uu____18204 = matches_pat t1 p1 in
                       (match uu____18204 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18253 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18359 = matches_pat scrutinee1 p1 in
                       (match uu____18359 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18399  ->
                                  let uu____18400 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18401 =
                                    let uu____18402 =
                                      FStar_List.map
                                        (fun uu____18412  ->
                                           match uu____18412 with
                                           | (uu____18417,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18402
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18400 uu____18401);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18448  ->
                                       match uu____18448 with
                                       | (bv,t1) ->
                                           let uu____18471 =
                                             let uu____18478 =
                                               let uu____18481 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18481 in
                                             let uu____18482 =
                                               let uu____18483 =
                                                 let uu____18514 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18514, false) in
                                               Clos uu____18483 in
                                             (uu____18478, uu____18482) in
                                           uu____18471 :: env2) env1 s in
                              let uu____18623 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____18623))) in
                 let uu____18624 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18624
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___184_18647  ->
                match uu___184_18647 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18651 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18657 -> d in
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
            let uu___250_18686 = config s e in
            {
              steps = (uu___250_18686.steps);
              tcenv = (uu___250_18686.tcenv);
              delta_level = (uu___250_18686.delta_level);
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
      fun t  -> let uu____18717 = config s e in norm_comp uu____18717 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18732 = config [] env in norm_universe uu____18732 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____18747 = config [] env in ghost_to_pure_aux uu____18747 [] c
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
        let uu____18767 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18767 in
      let uu____18774 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18774
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___251_18776 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___251_18776.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___251_18776.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____18779  ->
                    let uu____18780 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____18780))
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
            ((let uu____18799 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18799);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18812 = config [AllowUnboundUniverses] env in
          norm_comp uu____18812 [] c
        with
        | e ->
            ((let uu____18825 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____18825);
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
                   let uu____18865 =
                     let uu____18866 =
                       let uu____18873 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18873) in
                     FStar_Syntax_Syntax.Tm_refine uu____18866 in
                   mk uu____18865 t01.FStar_Syntax_Syntax.pos
               | uu____18878 -> t2)
          | uu____18879 -> t2 in
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
        let uu____18931 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18931 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18960 ->
                 let uu____18967 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18967 with
                  | (actuals,uu____18977,uu____18978) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18992 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18992 with
                         | (binders,args) ->
                             let uu____19009 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19009
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
      | uu____19019 ->
          let uu____19020 = FStar_Syntax_Util.head_and_args t in
          (match uu____19020 with
           | (head1,args) ->
               let uu____19057 =
                 let uu____19058 = FStar_Syntax_Subst.compress head1 in
                 uu____19058.FStar_Syntax_Syntax.n in
               (match uu____19057 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19061,thead) ->
                    let uu____19087 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19087 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19129 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___256_19137 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___256_19137.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___256_19137.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___256_19137.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___256_19137.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___256_19137.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___256_19137.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___256_19137.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___256_19137.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___256_19137.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___256_19137.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___256_19137.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___256_19137.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___256_19137.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___256_19137.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___256_19137.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___256_19137.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___256_19137.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___256_19137.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___256_19137.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___256_19137.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___256_19137.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___256_19137.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___256_19137.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___256_19137.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___256_19137.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___256_19137.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___256_19137.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___256_19137.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___256_19137.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___256_19137.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____19129 with
                            | (uu____19138,ty,uu____19140) ->
                                eta_expand_with_type env t ty))
                | uu____19141 ->
                    let uu____19142 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___257_19150 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___257_19150.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___257_19150.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___257_19150.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___257_19150.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___257_19150.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___257_19150.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___257_19150.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___257_19150.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___257_19150.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___257_19150.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___257_19150.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___257_19150.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___257_19150.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___257_19150.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___257_19150.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___257_19150.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___257_19150.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___257_19150.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___257_19150.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___257_19150.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___257_19150.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___257_19150.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___257_19150.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___257_19150.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___257_19150.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___257_19150.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___257_19150.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___257_19150.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___257_19150.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___257_19150.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____19142 with
                     | (uu____19151,ty,uu____19153) ->
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
            | (uu____19231,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19237,FStar_Util.Inl t) ->
                let uu____19243 =
                  let uu____19246 =
                    let uu____19247 =
                      let uu____19260 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19260) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19247 in
                  FStar_Syntax_Syntax.mk uu____19246 in
                uu____19243 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19264 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19264 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19291 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19346 ->
                    let uu____19347 =
                      let uu____19356 =
                        let uu____19357 = FStar_Syntax_Subst.compress t3 in
                        uu____19357.FStar_Syntax_Syntax.n in
                      (uu____19356, tc) in
                    (match uu____19347 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19382) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19419) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19458,FStar_Util.Inl uu____19459) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19482 -> failwith "Impossible") in
              (match uu____19291 with
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
          let uu____19591 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19591 with
          | (univ_names1,binders1,tc) ->
              let uu____19649 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19649)
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
          let uu____19688 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19688 with
          | (univ_names1,binders1,tc) ->
              let uu____19748 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19748)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19783 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19783 with
           | (univ_names1,binders1,typ1) ->
               let uu___258_19811 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___258_19811.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___258_19811.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___258_19811.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___258_19811.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___259_19832 = s in
          let uu____19833 =
            let uu____19834 =
              let uu____19843 = FStar_List.map (elim_uvars env) sigs in
              (uu____19843, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19834 in
          {
            FStar_Syntax_Syntax.sigel = uu____19833;
            FStar_Syntax_Syntax.sigrng =
              (uu___259_19832.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___259_19832.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___259_19832.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___259_19832.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19860 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19860 with
           | (univ_names1,uu____19878,typ1) ->
               let uu___260_19892 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___260_19892.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___260_19892.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___260_19892.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___260_19892.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19898 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19898 with
           | (univ_names1,uu____19916,typ1) ->
               let uu___261_19930 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___261_19930.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___261_19930.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___261_19930.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___261_19930.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19964 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19964 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19987 =
                            let uu____19988 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19988 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19987 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___262_19991 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___262_19991.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___262_19991.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___263_19992 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___263_19992.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___263_19992.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___263_19992.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___263_19992.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___264_20004 = s in
          let uu____20005 =
            let uu____20006 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20006 in
          {
            FStar_Syntax_Syntax.sigel = uu____20005;
            FStar_Syntax_Syntax.sigrng =
              (uu___264_20004.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___264_20004.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___264_20004.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___264_20004.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20010 = elim_uvars_aux_t env us [] t in
          (match uu____20010 with
           | (us1,uu____20028,t1) ->
               let uu___265_20042 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___265_20042.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___265_20042.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___265_20042.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___265_20042.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20043 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20045 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20045 with
           | (univs1,binders,signature) ->
               let uu____20073 =
                 let uu____20082 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20082 with
                 | (univs_opening,univs2) ->
                     let uu____20109 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20109) in
               (match uu____20073 with
                | (univs_opening,univs_closing) ->
                    let uu____20126 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20132 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20133 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20132, uu____20133) in
                    (match uu____20126 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20155 =
                           match uu____20155 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20173 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20173 with
                                | (us1,t1) ->
                                    let uu____20184 =
                                      let uu____20189 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20196 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20189, uu____20196) in
                                    (match uu____20184 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20209 =
                                           let uu____20214 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20223 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20214, uu____20223) in
                                         (match uu____20209 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20239 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20239 in
                                              let uu____20240 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20240 with
                                               | (uu____20261,uu____20262,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20277 =
                                                       let uu____20278 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20278 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20277 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20283 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20283 with
                           | (uu____20296,uu____20297,t1) -> t1 in
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
                             | uu____20357 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20374 =
                               let uu____20375 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20375.FStar_Syntax_Syntax.n in
                             match uu____20374 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20434 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20463 =
                               let uu____20464 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20464.FStar_Syntax_Syntax.n in
                             match uu____20463 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20485) ->
                                 let uu____20506 = destruct_action_body body in
                                 (match uu____20506 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20551 ->
                                 let uu____20552 = destruct_action_body t in
                                 (match uu____20552 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20601 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20601 with
                           | (action_univs,t) ->
                               let uu____20610 = destruct_action_typ_templ t in
                               (match uu____20610 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___266_20651 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___266_20651.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___266_20651.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___267_20653 = ed in
                           let uu____20654 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20655 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20656 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20657 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20658 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20659 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20660 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20661 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20662 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20663 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20664 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20665 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20666 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20667 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___267_20653.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___267_20653.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20654;
                             FStar_Syntax_Syntax.bind_wp = uu____20655;
                             FStar_Syntax_Syntax.if_then_else = uu____20656;
                             FStar_Syntax_Syntax.ite_wp = uu____20657;
                             FStar_Syntax_Syntax.stronger = uu____20658;
                             FStar_Syntax_Syntax.close_wp = uu____20659;
                             FStar_Syntax_Syntax.assert_p = uu____20660;
                             FStar_Syntax_Syntax.assume_p = uu____20661;
                             FStar_Syntax_Syntax.null_wp = uu____20662;
                             FStar_Syntax_Syntax.trivial = uu____20663;
                             FStar_Syntax_Syntax.repr = uu____20664;
                             FStar_Syntax_Syntax.return_repr = uu____20665;
                             FStar_Syntax_Syntax.bind_repr = uu____20666;
                             FStar_Syntax_Syntax.actions = uu____20667
                           } in
                         let uu___268_20670 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___268_20670.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___268_20670.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___268_20670.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___268_20670.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___185_20687 =
            match uu___185_20687 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20714 = elim_uvars_aux_t env us [] t in
                (match uu____20714 with
                 | (us1,uu____20738,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___269_20757 = sub_eff in
            let uu____20758 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20761 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___269_20757.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___269_20757.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20758;
              FStar_Syntax_Syntax.lift = uu____20761
            } in
          let uu___270_20764 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___270_20764.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___270_20764.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___270_20764.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___270_20764.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____20774 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20774 with
           | (univ_names1,binders1,comp1) ->
               let uu___271_20808 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___271_20808.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___271_20808.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___271_20808.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___271_20808.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20819 -> s