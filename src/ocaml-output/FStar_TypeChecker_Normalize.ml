open Prims
type step =
  | Beta
  | Iota
  | Zeta
  | Exclude of step
  | WHNF
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
let uu___is_WHNF: step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____48 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____53 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____63 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____68 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____74 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____90 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____109 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____114 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____119 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____124 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____129 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____139 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____144 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____149 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____154 -> false
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
    match projectee with | Clos _0 -> true | uu____383 -> false
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
    match projectee with | Univ _0 -> true | uu____487 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____500 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___169_520  ->
    match uu___169_520 with
    | Clos (uu____521,t,uu____523,uu____524) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____569 -> "Univ"
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
    let uu___186_662 = cfg in
    let uu____663 = only_strong_steps' cfg.primitive_steps in
    {
      steps = (uu___186_662.steps);
      tcenv = (uu___186_662.tcenv);
      delta_level = (uu___186_662.delta_level);
      primitive_steps = uu____663
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
    match projectee with | Arg _0 -> true | uu____810 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____848 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____886 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____945 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____989 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1047 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1089 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1123 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1171 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1219 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1248 .
    'Auu____1248 ->
      FStar_Range.range -> 'Auu____1248 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1405 'Auu____1406 .
    ('Auu____1406 FStar_Pervasives_Native.option,'Auu____1405) FStar_ST.mref
      -> 'Auu____1406 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1701 = FStar_ST.op_Bang r in
      match uu____1701 with
      | FStar_Pervasives_Native.Some uu____1802 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1909 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1909 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___170_1917  ->
    match uu___170_1917 with
    | Arg (c,uu____1919,uu____1920) ->
        let uu____1921 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1921
    | MemoLazy uu____1922 -> "MemoLazy"
    | Abs (uu____1929,bs,uu____1931,uu____1932,uu____1933) ->
        let uu____1938 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1938
    | UnivArgs uu____1943 -> "UnivArgs"
    | Match uu____1950 -> "Match"
    | App (uu____1957,t,uu____1959,uu____1960) ->
        let uu____1961 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1961
    | Meta (m,uu____1963) -> "Meta"
    | Let uu____1964 -> "Let"
    | Steps (uu____1973,uu____1974,uu____1975) -> "Steps"
    | Debug (t,uu____1985) ->
        let uu____1986 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1986
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1995 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1995 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____2013 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____2013 then f () else ()
let is_empty: 'Auu____2019 . 'Auu____2019 Prims.list -> Prims.bool =
  fun uu___171_2025  ->
    match uu___171_2025 with | [] -> true | uu____2028 -> false
let lookup_bvar:
  'Auu____2039 'Auu____2040 .
    ('Auu____2040,'Auu____2039) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2039
  =
  fun env  ->
    fun x  ->
      try
        let uu____2064 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____2064
      with
      | uu____2077 ->
          let uu____2078 =
            let uu____2079 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____2079 in
          failwith uu____2078
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
          let uu____2120 =
            FStar_List.fold_left
              (fun uu____2146  ->
                 fun u1  ->
                   match uu____2146 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2171 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____2171 with
                        | (k_u,n1) ->
                            let uu____2186 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____2186
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____2120 with
          | (uu____2204,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2229 =
                   let uu____2230 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____2230 in
                 match uu____2229 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2248 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2257 ->
                   let uu____2258 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2258
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2264 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2273 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2282 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2289 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2289 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2306 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2306 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2314 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2322 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2322 with
                                  | (uu____2327,m) -> n1 <= m)) in
                        if uu____2314 then rest1 else us1
                    | uu____2332 -> us1)
               | uu____2337 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2341 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2341 in
        let uu____2344 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2344
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2346 = aux u in
           match uu____2346 with
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
          (fun uu____2450  ->
             let uu____2451 = FStar_Syntax_Print.tag_of_term t in
             let uu____2452 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2451
               uu____2452);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2459 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2461 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2486 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2487 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2488 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2489 ->
                  let uu____2506 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2506
                  then
                    let uu____2507 =
                      let uu____2508 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2509 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2508 uu____2509 in
                    failwith uu____2507
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2512 =
                    let uu____2513 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2513 in
                  mk uu____2512 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2520 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2520
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2522 = lookup_bvar env x in
                  (match uu____2522 with
                   | Univ uu____2525 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2529) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2641 = closures_as_binders_delayed cfg env bs in
                  (match uu____2641 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2669 =
                         let uu____2670 =
                           let uu____2687 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2687) in
                         FStar_Syntax_Syntax.Tm_abs uu____2670 in
                       mk uu____2669 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2718 = closures_as_binders_delayed cfg env bs in
                  (match uu____2718 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2760 =
                    let uu____2771 =
                      let uu____2778 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2778] in
                    closures_as_binders_delayed cfg env uu____2771 in
                  (match uu____2760 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2796 =
                         let uu____2797 =
                           let uu____2804 =
                             let uu____2805 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2805
                               FStar_Pervasives_Native.fst in
                           (uu____2804, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2797 in
                       mk uu____2796 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2896 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2896
                    | FStar_Util.Inr c ->
                        let uu____2910 = close_comp cfg env c in
                        FStar_Util.Inr uu____2910 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2926 =
                    let uu____2927 =
                      let uu____2954 = closure_as_term_delayed cfg env t11 in
                      (uu____2954, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2927 in
                  mk uu____2926 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3005 =
                    let uu____3006 =
                      let uu____3013 = closure_as_term_delayed cfg env t' in
                      let uu____3016 =
                        let uu____3017 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____3017 in
                      (uu____3013, uu____3016) in
                    FStar_Syntax_Syntax.Tm_meta uu____3006 in
                  mk uu____3005 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3077 =
                    let uu____3078 =
                      let uu____3085 = closure_as_term_delayed cfg env t' in
                      let uu____3088 =
                        let uu____3089 =
                          let uu____3096 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____3096) in
                        FStar_Syntax_Syntax.Meta_monadic uu____3089 in
                      (uu____3085, uu____3088) in
                    FStar_Syntax_Syntax.Tm_meta uu____3078 in
                  mk uu____3077 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3115 =
                    let uu____3116 =
                      let uu____3123 = closure_as_term_delayed cfg env t' in
                      let uu____3126 =
                        let uu____3127 =
                          let uu____3136 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____3136) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3127 in
                      (uu____3123, uu____3126) in
                    FStar_Syntax_Syntax.Tm_meta uu____3116 in
                  mk uu____3115 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3149 =
                    let uu____3150 =
                      let uu____3157 = closure_as_term_delayed cfg env t' in
                      (uu____3157, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____3150 in
                  mk uu____3149 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3197  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____3216 =
                    let uu____3227 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____3227
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3246 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___191_3258 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___191_3258.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___191_3258.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3246)) in
                  (match uu____3216 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___192_3274 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___192_3274.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___192_3274.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3285,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3344  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3369 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3369
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3389  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3411 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3411
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___193_3423 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___193_3423.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___193_3423.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___194_3424 = lb in
                    let uu____3425 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___194_3424.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___194_3424.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3425
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3455  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3544 =
                    match uu____3544 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3599 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3620 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3680  ->
                                        fun uu____3681  ->
                                          match (uu____3680, uu____3681) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3772 =
                                                norm_pat env3 p1 in
                                              (match uu____3772 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3620 with
                               | (pats1,env3) ->
                                   ((let uu___195_3854 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___195_3854.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___196_3873 = x in
                                let uu____3874 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___196_3873.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___196_3873.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3874
                                } in
                              ((let uu___197_3888 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___197_3888.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___198_3899 = x in
                                let uu____3900 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___198_3899.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___198_3899.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3900
                                } in
                              ((let uu___199_3914 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___199_3914.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___200_3930 = x in
                                let uu____3931 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___200_3930.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___200_3930.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3931
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___201_3938 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___201_3938.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3941 = norm_pat env1 pat in
                        (match uu____3941 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3970 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3970 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3976 =
                    let uu____3977 =
                      let uu____4000 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____4000) in
                    FStar_Syntax_Syntax.Tm_match uu____3977 in
                  mk uu____3976 t1.FStar_Syntax_Syntax.pos))
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
        | uu____4086 -> closure_as_term cfg env t
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
        | uu____4112 ->
            FStar_List.map
              (fun uu____4129  ->
                 match uu____4129 with
                 | (x,imp) ->
                     let uu____4148 = closure_as_term_delayed cfg env x in
                     (uu____4148, imp)) args
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
        let uu____4162 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4211  ->
                  fun uu____4212  ->
                    match (uu____4211, uu____4212) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___202_4282 = b in
                          let uu____4283 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___202_4282.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___202_4282.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4283
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____4162 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4376 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4389 = closure_as_term_delayed cfg env t in
                 let uu____4390 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4389 uu____4390
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4403 = closure_as_term_delayed cfg env t in
                 let uu____4404 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4403 uu____4404
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
                        (fun uu___172_4430  ->
                           match uu___172_4430 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4434 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4434
                           | f -> f)) in
                 let uu____4438 =
                   let uu___203_4439 = c1 in
                   let uu____4440 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4440;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___203_4439.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4438)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___173_4450  ->
            match uu___173_4450 with
            | FStar_Syntax_Syntax.DECREASES uu____4451 -> false
            | uu____4454 -> true))
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
                   (fun uu___174_4472  ->
                      match uu___174_4472 with
                      | FStar_Syntax_Syntax.DECREASES uu____4473 -> false
                      | uu____4476 -> true)) in
            let rc1 =
              let uu___204_4478 = rc in
              let uu____4479 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___204_4478.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4479;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4486 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4507 =
      let uu____4508 =
        let uu____4519 = FStar_Util.string_of_int i in
        (uu____4519, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4508 in
    const_as_tm uu____4507 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b = const_as_tm (FStar_Const.Const_string (b, p)) p in
  let arg_as_int uu____4553 =
    match uu____4553 with
    | (a,uu____4561) ->
        let uu____4564 =
          let uu____4565 = FStar_Syntax_Subst.compress a in
          uu____4565.FStar_Syntax_Syntax.n in
        (match uu____4564 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4581 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4581
         | uu____4582 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4596 =
    match uu____4596 with
    | (a,uu____4608) ->
        let uu____4615 =
          let uu____4616 = FStar_Syntax_Subst.compress a in
          uu____4616.FStar_Syntax_Syntax.n in
        (match uu____4615 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4626;
                FStar_Syntax_Syntax.vars = uu____4627;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4629;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4630;_},uu____4631)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4670 =
               let uu____4675 = FStar_Util.int_of_string i in
               (fv1, uu____4675) in
             FStar_Pervasives_Native.Some uu____4670
         | uu____4680 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4694 =
    match uu____4694 with
    | (a,uu____4702) ->
        let uu____4705 =
          let uu____4706 = FStar_Syntax_Subst.compress a in
          uu____4706.FStar_Syntax_Syntax.n in
        (match uu____4705 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4712 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4722 =
    match uu____4722 with
    | (a,uu____4730) ->
        let uu____4733 =
          let uu____4734 = FStar_Syntax_Subst.compress a in
          uu____4734.FStar_Syntax_Syntax.n in
        (match uu____4733 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4740 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4750 =
    match uu____4750 with
    | (a,uu____4758) ->
        let uu____4761 =
          let uu____4762 = FStar_Syntax_Subst.compress a in
          uu____4762.FStar_Syntax_Syntax.n in
        (match uu____4761 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____4768)) -> FStar_Pervasives_Native.Some s
         | uu____4769 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4795 =
    match uu____4795 with
    | (a,uu____4809) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4838 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4855 = sequence xs in
              (match uu____4855 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4875 = FStar_Syntax_Util.list_elements a in
        (match uu____4875 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4893 =
               FStar_List.map
                 (fun x  ->
                    let uu____4903 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4903) elts in
             sequence uu____4893) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4941 = f a in FStar_Pervasives_Native.Some uu____4941
    | uu____4942 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4992 = f a0 a1 in FStar_Pervasives_Native.Some uu____4992
    | uu____4993 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res args =
    let uu____5042 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____5042 in
  let binary_op as_a f res args =
    let uu____5098 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____5098 in
  let as_primitive_step uu____5122 =
    match uu____5122 with
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
      (fun r  -> fun x  -> let uu____5170 = f x in int_as_const r uu____5170) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5198 = f x y in int_as_const r uu____5198) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____5219 = f x in bool_as_const r uu____5219) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5247 = f x y in bool_as_const r uu____5247) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____5275 = f x y in string_as_const r uu____5275) in
  let list_of_string' rng s =
    let name l =
      let uu____5289 =
        let uu____5290 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5290 in
      mk uu____5289 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5300 =
      let uu____5303 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5303 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5300 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5378 = arg_as_string a1 in
        (match uu____5378 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5384 = arg_as_list arg_as_string a2 in
             (match uu____5384 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5397 = string_as_const psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____5397
              | uu____5398 -> FStar_Pervasives_Native.None)
         | uu____5403 -> FStar_Pervasives_Native.None)
    | uu____5406 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5420 = FStar_Util.string_of_int i in
    string_as_const rng uu____5420 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5436 = FStar_Util.string_of_int i in
    string_as_const rng uu____5436 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5466 args =
    match args with
    | uu____5478::(t,uu____5480)::[] ->
        let uu____5509 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5509
    | uu____5514 -> FStar_Pervasives_Native.None in
  let set_range_of1 uu____5536 args =
    match args with
    | uu____5546::(t,uu____5548)::(r,uu____5550)::[] ->
        let uu____5571 = FStar_Syntax_Embeddings.unembed_range r in
        FStar_Util.bind_opt uu____5571
          (fun r1  ->
             FStar_Pervasives_Native.Some
               (let uu___205_5581 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___205_5581.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars =
                    (uu___205_5581.FStar_Syntax_Syntax.vars)
                }))
    | uu____5582 -> FStar_Pervasives_Native.None in
  let mk_range1 uu____5602 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5661 =
          let uu____5682 = arg_as_string fn in
          let uu____5685 = arg_as_int from_line in
          let uu____5688 = arg_as_int from_col in
          let uu____5691 = arg_as_int to_line in
          let uu____5694 = arg_as_int to_col in
          (uu____5682, uu____5685, uu____5688, uu____5691, uu____5694) in
        (match uu____5661 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5725 = FStar_Range.mk_pos from_l from_c in
               let uu____5726 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5725 uu____5726 in
             let uu____5727 = term_of_range r in
             FStar_Pervasives_Native.Some uu____5727
         | uu____5732 -> FStar_Pervasives_Native.None)
    | uu____5753 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____5784)::(a1,uu____5786)::(a2,uu____5788)::[] ->
        let uu____5825 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5825 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5838 -> FStar_Pervasives_Native.None)
    | uu____5839 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5857 =
      let uu____5872 =
        let uu____5887 =
          let uu____5902 =
            let uu____5917 =
              let uu____5932 =
                let uu____5947 =
                  let uu____5962 =
                    let uu____5977 =
                      let uu____5992 =
                        let uu____6007 =
                          let uu____6022 =
                            let uu____6037 =
                              let uu____6052 =
                                let uu____6067 =
                                  let uu____6082 =
                                    let uu____6097 =
                                      let uu____6112 =
                                        let uu____6127 =
                                          let uu____6142 =
                                            let uu____6157 =
                                              let uu____6170 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____6170,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____6177 =
                                              let uu____6192 =
                                                let uu____6205 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____6205,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____6214 =
                                                let uu____6229 =
                                                  let uu____6248 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____6248,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____6261 =
                                                  let uu____6282 =
                                                    let uu____6303 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6303,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6318 =
                                                    let uu____6341 =
                                                      let uu____6360 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6360,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6373 =
                                                      let uu____6394 =
                                                        let uu____6413 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6413,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6394] in
                                                    uu____6341 :: uu____6373 in
                                                  uu____6282 :: uu____6318 in
                                                uu____6229 :: uu____6261 in
                                              uu____6192 :: uu____6214 in
                                            uu____6157 :: uu____6177 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____6142 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____6127 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____6112 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____6097 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____6082 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6067 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6052 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6037 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6022 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6007 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5992 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5977 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5962 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5947 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5932 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5917 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5902 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5887 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5872 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5857 in
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
      let c = int_as_const r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____7018 =
        let uu____7019 =
          let uu____7020 = FStar_Syntax_Syntax.as_arg c in [uu____7020] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7019 in
      uu____7018 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____7055 =
              let uu____7068 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____7068, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____7087  ->
                        fun uu____7088  ->
                          match (uu____7087, uu____7088) with
                          | ((int_to_t1,x),(uu____7107,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____7117 =
              let uu____7132 =
                let uu____7145 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____7145, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____7164  ->
                          fun uu____7165  ->
                            match (uu____7164, uu____7165) with
                            | ((int_to_t1,x),(uu____7184,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____7194 =
                let uu____7209 =
                  let uu____7222 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____7222, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____7241  ->
                            fun uu____7242  ->
                              match (uu____7241, uu____7242) with
                              | ((int_to_t1,x),(uu____7261,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____7209] in
              uu____7132 :: uu____7194 in
            uu____7055 :: uu____7117)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____7360)::(a1,uu____7362)::(a2,uu____7364)::[] ->
        let uu____7401 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7401 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___206_7407 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___206_7407.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___206_7407.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___207_7411 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___207_7411.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___207_7411.FStar_Syntax_Syntax.vars)
                })
         | uu____7412 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7414)::uu____7415::(a1,uu____7417)::(a2,uu____7419)::[] ->
        let uu____7468 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7468 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___206_7474 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___206_7474.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___206_7474.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___207_7478 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___207_7478.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___207_7478.FStar_Syntax_Syntax.vars)
                })
         | uu____7479 -> FStar_Pervasives_Native.None)
    | uu____7480 -> failwith "Unexpected number of arguments" in
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
  'Auu____7491 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7491) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7551  ->
           fun subst1  ->
             match uu____7551 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,memo,uu____7593)) ->
                      let uu____7652 = b in
                      (match uu____7652 with
                       | (bv,uu____7660) ->
                           let uu____7661 =
                             let uu____7662 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7662 in
                           if uu____7661
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let x =
                                let uu____7668 =
                                  FStar_Syntax_Util.un_alien term1 in
                                FStar_All.pipe_right uu____7668
                                  FStar_Dyn.undyn in
                              let b1 =
                                let uu____7670 =
                                  let uu___208_7671 = bv in
                                  let uu____7672 =
                                    FStar_Syntax_Subst.subst subst1
                                      (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___208_7671.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___208_7671.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____7672
                                  } in
                                FStar_Syntax_Syntax.freshen_bv uu____7670 in
                              let b_for_x =
                                let uu____7676 =
                                  let uu____7683 =
                                    FStar_Syntax_Syntax.bv_to_name b1 in
                                  ((FStar_Pervasives_Native.fst x),
                                    uu____7683) in
                                FStar_Syntax_Syntax.NT uu____7676 in
                              let subst2 =
                                FStar_List.filter
                                  (fun uu___175_7692  ->
                                     match uu___175_7692 with
                                     | FStar_Syntax_Syntax.NT
                                         (uu____7693,{
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_name
                                                         b';
                                                       FStar_Syntax_Syntax.pos
                                                         = uu____7695;
                                                       FStar_Syntax_Syntax.vars
                                                         = uu____7696;_})
                                         ->
                                         Prims.op_Negation
                                           (FStar_Ident.ident_equals
                                              b1.FStar_Syntax_Syntax.ppname
                                              b'.FStar_Syntax_Syntax.ppname)
                                     | uu____7701 -> true) subst1 in
                              b_for_x :: subst2))
                  | uu____7702 -> subst1)) env []
let reduce_primops:
  'Auu____7725 'Auu____7726 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7726) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7725 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let uu____7767 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7767
          then tm
          else
            (let uu____7769 = FStar_Syntax_Util.head_and_args tm in
             match uu____7769 with
             | (head1,args) ->
                 let uu____7806 =
                   let uu____7807 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7807.FStar_Syntax_Syntax.n in
                 (match uu____7806 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7811 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7811 with
                       | FStar_Pervasives_Native.None  -> tm
                       | FStar_Pervasives_Native.Some prim_step ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log cfg
                                (fun uu____7828  ->
                                   let uu____7829 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7830 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7837 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7829 uu____7830 uu____7837);
                              tm)
                           else
                             (log cfg
                                (fun uu____7842  ->
                                   let uu____7843 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7843);
                              (let psc =
                                 let uu____7845 =
                                   if prim_step.requires_binder_substitution
                                   then mk_psc_subst cfg env
                                   else [] in
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst = uu____7845
                                 } in
                               let uu____7847 =
                                 prim_step.interpretation psc args in
                               match uu____7847 with
                               | FStar_Pervasives_Native.None  ->
                                   (log cfg
                                      (fun uu____7853  ->
                                         let uu____7854 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7854);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log cfg
                                      (fun uu____7860  ->
                                         let uu____7861 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7862 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7861 uu____7862);
                                    reduced))))
                  | uu____7863 -> tm))
let reduce_equality:
  'Auu____7874 'Auu____7875 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7875) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7874 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___209_7913 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___209_7913.tcenv);
           delta_level = (uu___209_7913.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  'Auu____7926 'Auu____7927 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7927) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7926 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack1 tm in
          let uu____7969 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7969
          then tm1
          else
            (let w t =
               let uu___210_7981 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___210_7981.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___210_7981.FStar_Syntax_Syntax.vars)
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
               | uu____7998 -> FStar_Pervasives_Native.None in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8038;
                         FStar_Syntax_Syntax.vars = uu____8039;_},uu____8040);
                    FStar_Syntax_Syntax.pos = uu____8041;
                    FStar_Syntax_Syntax.vars = uu____8042;_},args)
                 ->
                 let uu____8068 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8068
                 then
                   let uu____8069 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8069 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8124)::
                        (uu____8125,(arg,uu____8127))::[] -> arg
                    | (uu____8192,(arg,uu____8194))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8195)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8260)::uu____8261::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8324::(FStar_Pervasives_Native.Some (false
                                   ),uu____8325)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8388 -> tm1)
                 else
                   (let uu____8404 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8404
                    then
                      let uu____8405 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8405 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8460)::uu____8461::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8524::(FStar_Pervasives_Native.Some (true
                                     ),uu____8525)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8588)::
                          (uu____8589,(arg,uu____8591))::[] -> arg
                      | (uu____8656,(arg,uu____8658))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8659)::[]
                          -> arg
                      | uu____8724 -> tm1
                    else
                      (let uu____8740 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8740
                       then
                         let uu____8741 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8741 with
                         | uu____8796::(FStar_Pervasives_Native.Some (true
                                        ),uu____8797)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8860)::uu____8861::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8924)::
                             (uu____8925,(arg,uu____8927))::[] -> arg
                         | (uu____8992,(p,uu____8994))::(uu____8995,(q,uu____8997))::[]
                             ->
                             let uu____9062 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9062
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____9064 -> tm1
                       else
                         (let uu____9080 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9080
                          then
                            let uu____9081 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9081 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9136)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9175)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9214 -> tm1
                          else
                            (let uu____9230 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____9230
                             then
                               match args with
                               | (t,uu____9232)::[] ->
                                   let uu____9249 =
                                     let uu____9250 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9250.FStar_Syntax_Syntax.n in
                                   (match uu____9249 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9253::[],body,uu____9255) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9282 -> tm1)
                                    | uu____9285 -> tm1)
                               | (uu____9286,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9287))::
                                   (t,uu____9289)::[] ->
                                   let uu____9328 =
                                     let uu____9329 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____9329.FStar_Syntax_Syntax.n in
                                   (match uu____9328 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9332::[],body,uu____9334) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9361 -> tm1)
                                    | uu____9364 -> tm1)
                               | uu____9365 -> tm1
                             else
                               (let uu____9375 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9375
                                then
                                  match args with
                                  | (t,uu____9377)::[] ->
                                      let uu____9394 =
                                        let uu____9395 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9395.FStar_Syntax_Syntax.n in
                                      (match uu____9394 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9398::[],body,uu____9400)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9427 -> tm1)
                                       | uu____9430 -> tm1)
                                  | (uu____9431,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9432))::(t,uu____9434)::[] ->
                                      let uu____9473 =
                                        let uu____9474 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9474.FStar_Syntax_Syntax.n in
                                      (match uu____9473 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9477::[],body,uu____9479)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9506 -> tm1)
                                       | uu____9509 -> tm1)
                                  | uu____9510 -> tm1
                                else
                                  (let uu____9520 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9520
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9521;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9522;_},uu____9523)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9540;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9541;_},uu____9542)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9559 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9570;
                    FStar_Syntax_Syntax.vars = uu____9571;_},args)
                 ->
                 let uu____9593 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9593
                 then
                   let uu____9594 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9594 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9649)::
                        (uu____9650,(arg,uu____9652))::[] -> arg
                    | (uu____9717,(arg,uu____9719))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9720)::[]
                        -> arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9785)::uu____9786::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9849::(FStar_Pervasives_Native.Some (false
                                   ),uu____9850)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9913 -> tm1)
                 else
                   (let uu____9929 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9929
                    then
                      let uu____9930 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9930 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9985)::uu____9986::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10049::(FStar_Pervasives_Native.Some (true
                                      ),uu____10050)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____10113)::
                          (uu____10114,(arg,uu____10116))::[] -> arg
                      | (uu____10181,(arg,uu____10183))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____10184)::[]
                          -> arg
                      | uu____10249 -> tm1
                    else
                      (let uu____10265 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____10265
                       then
                         let uu____10266 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____10266 with
                         | uu____10321::(FStar_Pervasives_Native.Some (true
                                         ),uu____10322)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10385)::uu____10386::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10449)::
                             (uu____10450,(arg,uu____10452))::[] -> arg
                         | (uu____10517,(p,uu____10519))::(uu____10520,
                                                           (q,uu____10522))::[]
                             ->
                             let uu____10587 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10587
                              then w FStar_Syntax_Util.t_true
                              else tm1)
                         | uu____10589 -> tm1
                       else
                         (let uu____10605 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10605
                          then
                            let uu____10606 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10606 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10661)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10700)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10739 -> tm1
                          else
                            (let uu____10755 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10755
                             then
                               match args with
                               | (t,uu____10757)::[] ->
                                   let uu____10774 =
                                     let uu____10775 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10775.FStar_Syntax_Syntax.n in
                                   (match uu____10774 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10778::[],body,uu____10780) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10807 -> tm1)
                                    | uu____10810 -> tm1)
                               | (uu____10811,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10812))::
                                   (t,uu____10814)::[] ->
                                   let uu____10853 =
                                     let uu____10854 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10854.FStar_Syntax_Syntax.n in
                                   (match uu____10853 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10857::[],body,uu____10859) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10886 -> tm1)
                                    | uu____10889 -> tm1)
                               | uu____10890 -> tm1
                             else
                               (let uu____10900 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10900
                                then
                                  match args with
                                  | (t,uu____10902)::[] ->
                                      let uu____10919 =
                                        let uu____10920 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10920.FStar_Syntax_Syntax.n in
                                      (match uu____10919 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10923::[],body,uu____10925)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10952 -> tm1)
                                       | uu____10955 -> tm1)
                                  | (uu____10956,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10957))::(t,uu____10959)::[] ->
                                      let uu____10998 =
                                        let uu____10999 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10999.FStar_Syntax_Syntax.n in
                                      (match uu____10998 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11002::[],body,uu____11004)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11031 -> tm1)
                                       | uu____11034 -> tm1)
                                  | uu____11035 -> tm1
                                else
                                  (let uu____11045 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____11045
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11046;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11047;_},uu____11048)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11065;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11066;_},uu____11067)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11084 -> tm1
                                   else reduce_equality cfg env stack1 tm1))))))
             | uu____11094 -> tm1)
let is_norm_request:
  'Auu____11101 .
    FStar_Syntax_Syntax.term -> 'Auu____11101 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11114 =
        let uu____11121 =
          let uu____11122 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11122.FStar_Syntax_Syntax.n in
        (uu____11121, args) in
      match uu____11114 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11128::uu____11129::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11133::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11138::uu____11139::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11142 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___176_11154  ->
    match uu___176_11154 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11160 =
          let uu____11163 =
            let uu____11164 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____11164 in
          [uu____11163] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____11160
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____11183 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____11183) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11221 =
          let uu____11224 =
            FStar_Syntax_Embeddings.unembed_list
              FStar_Syntax_Embeddings.unembed_norm_step s in
          FStar_All.pipe_right uu____11224 FStar_Util.must in
        FStar_All.pipe_right uu____11221 tr_norm_steps in
      match args with
      | uu____11247::(tm,uu____11249)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11272)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11287)::uu____11288::(tm,uu____11290)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11330 =
              let uu____11333 = full_norm steps in parse_steps uu____11333 in
            Beta :: uu____11330 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11342 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___177_11360  ->
    match uu___177_11360 with
    | (App
        (uu____11363,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11364;
                       FStar_Syntax_Syntax.vars = uu____11365;_},uu____11366,uu____11367))::uu____11368
        -> true
    | uu____11375 -> false
let firstn:
  'Auu____11384 .
    Prims.int ->
      'Auu____11384 Prims.list ->
        ('Auu____11384 Prims.list,'Auu____11384 Prims.list)
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
          (uu____11422,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11423;
                         FStar_Syntax_Syntax.vars = uu____11424;_},uu____11425,uu____11426))::uu____11427
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11434 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11550  ->
               let uu____11551 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11552 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11553 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11560 =
                 let uu____11561 =
                   let uu____11564 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11564 in
                 stack_to_string uu____11561 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11551 uu____11552 uu____11553 uu____11560);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11587 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11612 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11629 =
                 let uu____11630 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11631 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11630 uu____11631 in
               failwith uu____11629
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11632 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____11649 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____11650 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11651;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11652;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11655;
                 FStar_Syntax_Syntax.fv_delta = uu____11656;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11657;
                 FStar_Syntax_Syntax.fv_delta = uu____11658;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11659);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11667 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11667 ->
               let b = should_reify cfg stack1 in
               (log cfg
                  (fun uu____11673  ->
                     let uu____11674 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11675 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11674 uu____11675);
                if b
                then
                  (let uu____11676 = FStar_List.tl stack1 in
                   do_unfold_fv cfg env uu____11676 t1 fv)
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
                 let uu___211_11715 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___211_11715.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___211_11715.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11748 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11748) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___212_11756 = cfg in
                 let uu____11757 =
                   FStar_List.filter
                     (fun uu___178_11760  ->
                        match uu___178_11760 with
                        | UnfoldOnly uu____11761 -> false
                        | NoDeltaSteps  -> false
                        | uu____11764 -> true) cfg.steps in
                 {
                   steps = uu____11757;
                   tcenv = (uu___212_11756.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___212_11756.primitive_steps)
                 } in
               let uu____11765 = get_norm_request (norm cfg' env []) args in
               (match uu____11765 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11781 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___179_11786  ->
                                match uu___179_11786 with
                                | UnfoldUntil uu____11787 -> true
                                | UnfoldOnly uu____11788 -> true
                                | uu____11791 -> false)) in
                      if uu____11781
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___213_11796 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___213_11796.tcenv);
                        delta_level;
                        primitive_steps = (uu___213_11796.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11807 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11807
                      then
                        let uu____11810 =
                          let uu____11811 =
                            let uu____11816 = FStar_Util.now () in
                            (t1, uu____11816) in
                          Debug uu____11811 in
                        uu____11810 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11818;
                  FStar_Syntax_Syntax.vars = uu____11819;_},a1::a2::rest)
               ->
               let uu____11867 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11867 with
                | (hd1,uu____11883) ->
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
                    (FStar_Const.Const_reflect uu____11948);
                  FStar_Syntax_Syntax.pos = uu____11949;
                  FStar_Syntax_Syntax.vars = uu____11950;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11982 = FStar_List.tl stack1 in
               norm cfg env uu____11982 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11985;
                  FStar_Syntax_Syntax.vars = uu____11986;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____12018 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____12018 with
                | (reify_head,uu____12034) ->
                    let a1 =
                      let uu____12056 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____12056 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____12059);
                            FStar_Syntax_Syntax.pos = uu____12060;
                            FStar_Syntax_Syntax.vars = uu____12061;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____12095 ->
                         let stack2 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____12105 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____12105
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____12112 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____12112
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____12115 =
                      let uu____12122 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____12122, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____12115 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___180_12135  ->
                         match uu___180_12135 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____12138 =
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
                 if uu____12138
                 then false
                 else
                   (let uu____12140 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___181_12147  ->
                              match uu___181_12147 with
                              | UnfoldOnly uu____12148 -> true
                              | uu____12151 -> false)) in
                    match uu____12140 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____12155 -> should_delta) in
               (log cfg
                  (fun uu____12163  ->
                     let uu____12164 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____12165 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____12166 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____12164 uu____12165 uu____12166);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else do_unfold_fv cfg env stack1 t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12169 = lookup_bvar env x in
               (match uu____12169 with
                | Univ uu____12172 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____12221 = FStar_ST.op_Bang r in
                      (match uu____12221 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12358  ->
                                 let uu____12359 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____12360 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12359
                                   uu____12360);
                            (let uu____12361 =
                               let uu____12362 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____12362.FStar_Syntax_Syntax.n in
                             match uu____12361 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12365 ->
                                 norm cfg env2 stack1 t'
                             | uu____12382 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____12440)::uu____12441 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12450)::uu____12451 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12461,uu____12462))::stack_rest ->
                    (match c with
                     | Univ uu____12466 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12475 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12496  ->
                                    let uu____12497 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12497);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12537  ->
                                    let uu____12538 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12538);
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
                      (let uu___214_12588 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___214_12588.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____12673  ->
                          let uu____12674 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12674);
                     norm cfg env stack2 t1)
                | (Debug uu____12675)::uu____12676 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12683 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12683
                    else
                      (let uu____12685 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12685 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12727  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12755 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12755
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12765 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12765)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_12770 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_12770.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_12770.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12771 -> lopt in
                           (log cfg
                              (fun uu____12777  ->
                                 let uu____12778 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12778);
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
                | (Meta uu____12801)::uu____12802 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12809 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12809
                    else
                      (let uu____12811 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12811 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12853  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12881 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12881
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12891 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12891)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_12896 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_12896.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_12896.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12897 -> lopt in
                           (log cfg
                              (fun uu____12903  ->
                                 let uu____12904 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12904);
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
                | (Let uu____12927)::uu____12928 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12939 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12939
                    else
                      (let uu____12941 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12941 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12983  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13011 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13011
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13021 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13021)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_13026 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_13026.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_13026.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13027 -> lopt in
                           (log cfg
                              (fun uu____13033  ->
                                 let uu____13034 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13034);
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
                | (App uu____13057)::uu____13058 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____13069 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13069
                    else
                      (let uu____13071 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13071 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13113  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13141 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13141
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13151 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13151)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_13156 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_13156.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_13156.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13157 -> lopt in
                           (log cfg
                              (fun uu____13163  ->
                                 let uu____13164 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13164);
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
                | (Abs uu____13187)::uu____13188 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____13203 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13203
                    else
                      (let uu____13205 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13205 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13247  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13275 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13275
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13285 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13285)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_13290 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_13290.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_13290.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13291 -> lopt in
                           (log cfg
                              (fun uu____13297  ->
                                 let uu____13298 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13298);
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
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____13321 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13321
                    else
                      (let uu____13323 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____13323 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13365  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13393 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____13393
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13403 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____13403)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___215_13408 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___215_13408.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___215_13408.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13409 -> lopt in
                           (log cfg
                              (fun uu____13415  ->
                                 let uu____13416 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13416);
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
                      (fun uu____13477  ->
                         fun stack2  ->
                           match uu____13477 with
                           | (a,aq) ->
                               let uu____13489 =
                                 let uu____13490 =
                                   let uu____13497 =
                                     let uu____13498 =
                                       let uu____13529 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____13529, false) in
                                     Clos uu____13498 in
                                   (uu____13497, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____13490 in
                               uu____13489 :: stack2) args) in
               (log cfg
                  (fun uu____13605  ->
                     let uu____13606 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13606);
                norm cfg env stack2 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 (match (env, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___216_13642 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___216_13642.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___216_13642.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____13643 ->
                      let uu____13648 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____13648)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13651 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13651 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13682 =
                          let uu____13683 =
                            let uu____13690 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___217_13692 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___217_13692.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___217_13692.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13690) in
                          FStar_Syntax_Syntax.Tm_refine uu____13683 in
                        mk uu____13682 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____13711 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____13711
               else
                 (let uu____13713 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13713 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13721 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13745  -> dummy :: env1) env) in
                        norm_comp cfg uu____13721 c1 in
                      let t2 =
                        let uu____13767 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13767 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____13826)::uu____13827 -> norm cfg env stack1 t11
                | (Arg uu____13836)::uu____13837 -> norm cfg env stack1 t11
                | (App
                    (uu____13846,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13847;
                                   FStar_Syntax_Syntax.vars = uu____13848;_},uu____13849,uu____13850))::uu____13851
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____13858)::uu____13859 ->
                    norm cfg env stack1 t11
                | uu____13868 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____13872  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____13889 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____13889
                        | FStar_Util.Inr c ->
                            let uu____13897 = norm_comp cfg env c in
                            FStar_Util.Inr uu____13897 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____13903 =
                        let uu____13904 =
                          let uu____13905 =
                            let uu____13932 = FStar_Syntax_Util.unascribe t12 in
                            (uu____13932, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____13905 in
                        mk uu____13904 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____13903)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14008,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14009;
                               FStar_Syntax_Syntax.lbunivs = uu____14010;
                               FStar_Syntax_Syntax.lbtyp = uu____14011;
                               FStar_Syntax_Syntax.lbeff = uu____14012;
                               FStar_Syntax_Syntax.lbdef = uu____14013;_}::uu____14014),uu____14015)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____14051 =
                 (let uu____14054 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____14054) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____14056 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____14056))) in
               if uu____14051
               then
                 let binder =
                   let uu____14058 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____14058 in
                 let env1 =
                   let uu____14068 =
                     let uu____14075 =
                       let uu____14076 =
                         let uu____14107 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14107,
                           false) in
                       Clos uu____14076 in
                     ((FStar_Pervasives_Native.Some binder), uu____14075) in
                   uu____14068 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____14191 =
                    let uu____14196 =
                      let uu____14197 =
                        let uu____14198 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____14198
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____14197] in
                    FStar_Syntax_Subst.open_term uu____14196 body in
                  match uu____14191 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____14212 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____14212 in
                        FStar_Util.Inl
                          (let uu___218_14222 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___218_14222.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___218_14222.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___219_14224 = lb in
                        let uu____14225 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___219_14224.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___219_14224.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____14225
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____14260  -> dummy :: env1)
                             env) in
                      let cfg1 = only_strong_steps cfg in
                      norm cfg1 env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____14296 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____14296 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____14332 =
                               let uu___220_14333 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___220_14333.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___220_14333.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____14332 in
                           let uu____14334 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____14334 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____14360 =
                                   FStar_List.map (fun uu____14376  -> dummy)
                                     lbs1 in
                                 let uu____14377 =
                                   let uu____14386 =
                                     FStar_List.map
                                       (fun uu____14406  -> dummy) xs1 in
                                   FStar_List.append uu____14386 env in
                                 FStar_List.append uu____14360 uu____14377 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14430 =
                                       let uu___221_14431 = rc in
                                       let uu____14432 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___221_14431.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14432;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___221_14431.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14430
                                 | uu____14439 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___222_14443 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___222_14443.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___222_14443.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14453 =
                        FStar_List.map (fun uu____14469  -> dummy) lbs2 in
                      FStar_List.append uu____14453 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14477 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14477 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___223_14493 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___223_14493.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___223_14493.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14520 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____14520
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14539 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14615  ->
                        match uu____14615 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___224_14736 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___224_14736.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___224_14736.FStar_Syntax_Syntax.sort)
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
               (match uu____14539 with
                | (rec_env,memos,uu____14933) ->
                    let uu____14986 =
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
                             let uu____15517 =
                               let uu____15524 =
                                 let uu____15525 =
                                   let uu____15556 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15556, false) in
                                 Clos uu____15525 in
                               (FStar_Pervasives_Native.None, uu____15524) in
                             uu____15517 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15661 =
                      let uu____15662 = should_reify cfg stack1 in
                      Prims.op_Negation uu____15662 in
                    if uu____15661
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____15672 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____15672
                        then
                          let uu___225_15673 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___225_15673.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___225_15673.primitive_steps)
                          }
                        else
                          (let uu___226_15675 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___226_15675.tcenv);
                             delta_level = (uu___226_15675.delta_level);
                             primitive_steps =
                               (uu___226_15675.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____15677 =
                         let uu____15678 = FStar_Syntax_Subst.compress head1 in
                         uu____15678.FStar_Syntax_Syntax.n in
                       match uu____15677 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15696 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15696 with
                            | (uu____15697,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15703 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15711 =
                                         let uu____15712 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15712.FStar_Syntax_Syntax.n in
                                       match uu____15711 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15718,uu____15719))
                                           ->
                                           let uu____15728 =
                                             let uu____15729 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15729.FStar_Syntax_Syntax.n in
                                           (match uu____15728 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15735,msrc,uu____15737))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15746 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15746
                                            | uu____15747 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15748 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15749 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15749 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___227_15754 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___227_15754.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___227_15754.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___227_15754.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____15755 =
                                            FStar_List.tl stack1 in
                                          let uu____15756 =
                                            let uu____15757 =
                                              let uu____15760 =
                                                let uu____15761 =
                                                  let uu____15774 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____15774) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15761 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15760 in
                                            uu____15757
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____15755
                                            uu____15756
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15790 =
                                            let uu____15791 = is_return body in
                                            match uu____15791 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15795;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15796;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15801 -> false in
                                          if uu____15790
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
                                               let uu____15825 =
                                                 let uu____15828 =
                                                   let uu____15829 =
                                                     let uu____15846 =
                                                       let uu____15849 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____15849] in
                                                     (uu____15846, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15829 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15828 in
                                               uu____15825
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____15865 =
                                                 let uu____15866 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15866.FStar_Syntax_Syntax.n in
                                               match uu____15865 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15872::uu____15873::[])
                                                   ->
                                                   let uu____15880 =
                                                     let uu____15883 =
                                                       let uu____15884 =
                                                         let uu____15891 =
                                                           let uu____15894 =
                                                             let uu____15895
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15895 in
                                                           let uu____15896 =
                                                             let uu____15899
                                                               =
                                                               let uu____15900
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15900 in
                                                             [uu____15899] in
                                                           uu____15894 ::
                                                             uu____15896 in
                                                         (bind1, uu____15891) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15884 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15883 in
                                                   uu____15880
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15908 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____15914 =
                                                 let uu____15917 =
                                                   let uu____15918 =
                                                     let uu____15933 =
                                                       let uu____15936 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____15937 =
                                                         let uu____15940 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____15941 =
                                                           let uu____15944 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____15945 =
                                                             let uu____15948
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____15949
                                                               =
                                                               let uu____15952
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____15953
                                                                 =
                                                                 let uu____15956
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____15956] in
                                                               uu____15952 ::
                                                                 uu____15953 in
                                                             uu____15948 ::
                                                               uu____15949 in
                                                           uu____15944 ::
                                                             uu____15945 in
                                                         uu____15940 ::
                                                           uu____15941 in
                                                       uu____15936 ::
                                                         uu____15937 in
                                                     (bind_inst, uu____15933) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15918 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15917 in
                                               uu____15914
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____15964 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____15964 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____15988 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____15988 with
                            | (uu____15989,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____16024 =
                                        let uu____16025 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____16025.FStar_Syntax_Syntax.n in
                                      match uu____16024 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____16031) -> t4
                                      | uu____16036 -> head2 in
                                    let uu____16037 =
                                      let uu____16038 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____16038.FStar_Syntax_Syntax.n in
                                    match uu____16037 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____16044 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____16045 = maybe_extract_fv head2 in
                                  match uu____16045 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____16055 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____16055
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____16060 =
                                          maybe_extract_fv head3 in
                                        match uu____16060 with
                                        | FStar_Pervasives_Native.Some
                                            uu____16065 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____16066 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____16071 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____16086 =
                                    match uu____16086 with
                                    | (e,q) ->
                                        let uu____16093 =
                                          let uu____16094 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____16094.FStar_Syntax_Syntax.n in
                                        (match uu____16093 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____16109 -> false) in
                                  let uu____16110 =
                                    let uu____16111 =
                                      let uu____16118 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____16118 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____16111 in
                                  if uu____16110
                                  then
                                    let uu____16123 =
                                      let uu____16124 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____16124 in
                                    failwith uu____16123
                                  else ());
                                 (let uu____16126 =
                                    maybe_unfold_action head_app in
                                  match uu____16126 with
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
                                      let uu____16165 = FStar_List.tl stack1 in
                                      norm cfg env uu____16165 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____16179 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____16179 in
                           let uu____16180 = FStar_List.tl stack1 in
                           norm cfg env uu____16180 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16301  ->
                                     match uu____16301 with
                                     | (pat,wopt,tm) ->
                                         let uu____16349 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____16349))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____16381 = FStar_List.tl stack1 in
                           norm cfg env uu____16381 tm
                       | uu____16382 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16390 = should_reify cfg stack1 in
                    if uu____16390
                    then
                      let uu____16391 = FStar_List.tl stack1 in
                      let uu____16392 =
                        let uu____16393 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____16393 in
                      norm cfg env uu____16391 uu____16392
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____16396 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____16396
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___228_16405 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___228_16405.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___228_16405.primitive_steps)
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
                | uu____16407 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack1 head1
                    else
                      (match stack1 with
                       | uu____16409::uu____16410 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16415) ->
                                norm cfg env ((Meta (m, r)) :: stack1) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16416 ->
                                rebuild cfg env stack1 t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) head1
                            | uu____16447 -> norm cfg env stack1 head1)
                       | [] ->
                           let head2 = norm cfg env [] head1 in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16461 =
                                   norm_pattern_args cfg env args in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16461
                             | uu____16472 -> m in
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
              let uu____16484 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16484 in
            let uu____16485 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____16485 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16498  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack1 t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16509  ->
                      let uu____16510 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____16511 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16510
                        uu____16511);
                 (let t1 =
                    let uu____16513 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)) in
                    if uu____16513
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
                    | (UnivArgs (us',uu____16523))::stack2 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack2 t1
                    | uu____16578 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack1 t1
                    | uu____16581 ->
                        let uu____16584 =
                          let uu____16585 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16585 in
                        failwith uu____16584
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
              let uu____16595 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____16595 with
              | (uu____16596,return_repr) ->
                  let return_inst =
                    let uu____16605 =
                      let uu____16606 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____16606.FStar_Syntax_Syntax.n in
                    match uu____16605 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16612::[]) ->
                        let uu____16619 =
                          let uu____16622 =
                            let uu____16623 =
                              let uu____16630 =
                                let uu____16633 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____16633] in
                              (return_tm, uu____16630) in
                            FStar_Syntax_Syntax.Tm_uinst uu____16623 in
                          FStar_Syntax_Syntax.mk uu____16622 in
                        uu____16619 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16641 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____16644 =
                    let uu____16647 =
                      let uu____16648 =
                        let uu____16663 =
                          let uu____16666 = FStar_Syntax_Syntax.as_arg t in
                          let uu____16667 =
                            let uu____16670 = FStar_Syntax_Syntax.as_arg e in
                            [uu____16670] in
                          uu____16666 :: uu____16667 in
                        (return_inst, uu____16663) in
                      FStar_Syntax_Syntax.Tm_app uu____16648 in
                    FStar_Syntax_Syntax.mk uu____16647 in
                  uu____16644 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16679 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16679 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16682 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16682
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16683;
                     FStar_TypeChecker_Env.mtarget = uu____16684;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16685;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16696;
                     FStar_TypeChecker_Env.mtarget = uu____16697;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16698;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16716 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____16716)
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
                (fun uu____16772  ->
                   match uu____16772 with
                   | (a,imp) ->
                       let uu____16783 = norm cfg env [] a in
                       (uu____16783, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___229_16800 = comp1 in
            let uu____16803 =
              let uu____16804 =
                let uu____16813 = norm cfg env [] t in
                let uu____16814 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16813, uu____16814) in
              FStar_Syntax_Syntax.Total uu____16804 in
            {
              FStar_Syntax_Syntax.n = uu____16803;
              FStar_Syntax_Syntax.pos =
                (uu___229_16800.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___229_16800.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___230_16829 = comp1 in
            let uu____16832 =
              let uu____16833 =
                let uu____16842 = norm cfg env [] t in
                let uu____16843 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16842, uu____16843) in
              FStar_Syntax_Syntax.GTotal uu____16833 in
            {
              FStar_Syntax_Syntax.n = uu____16832;
              FStar_Syntax_Syntax.pos =
                (uu___230_16829.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___230_16829.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16895  ->
                      match uu____16895 with
                      | (a,i) ->
                          let uu____16906 = norm cfg env [] a in
                          (uu____16906, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___182_16917  ->
                      match uu___182_16917 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16921 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16921
                      | f -> f)) in
            let uu___231_16925 = comp1 in
            let uu____16928 =
              let uu____16929 =
                let uu___232_16930 = ct in
                let uu____16931 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16932 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16935 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16931;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___232_16930.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16932;
                  FStar_Syntax_Syntax.effect_args = uu____16935;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____16929 in
            {
              FStar_Syntax_Syntax.n = uu____16928;
              FStar_Syntax_Syntax.pos =
                (uu___231_16925.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___231_16925.FStar_Syntax_Syntax.vars)
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
            (let uu___233_16953 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___233_16953.tcenv);
               delta_level = (uu___233_16953.delta_level);
               primitive_steps = (uu___233_16953.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____16958 = norm1 t in
          FStar_Syntax_Util.non_informative uu____16958 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____16961 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___234_16980 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___234_16980.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___234_16980.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____16987 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____16987
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
                    let uu___235_16998 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___235_16998.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___235_16998.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___235_16998.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___236_17000 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___236_17000.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___236_17000.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___236_17000.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___236_17000.FStar_Syntax_Syntax.flags)
                    } in
              let uu___237_17001 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___237_17001.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___237_17001.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____17003 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____17006  ->
        match uu____17006 with
        | (x,imp) ->
            let uu____17009 =
              let uu___238_17010 = x in
              let uu____17011 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___238_17010.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___238_17010.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17011
              } in
            (uu____17009, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17017 =
          FStar_List.fold_left
            (fun uu____17035  ->
               fun b  ->
                 match uu____17035 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____17017 with | (nbs,uu____17075) -> FStar_List.rev nbs
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
            let uu____17091 =
              let uu___239_17092 = rc in
              let uu____17093 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___239_17092.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17093;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___239_17092.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17091
        | uu____17100 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          log cfg
            (fun uu____17113  ->
               let uu____17114 = FStar_Syntax_Print.tag_of_term t in
               let uu____17115 = FStar_Syntax_Print.term_to_string t in
               let uu____17116 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____17123 =
                 let uu____17124 =
                   let uu____17127 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17127 in
                 stack_to_string uu____17124 in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____17114 uu____17115 uu____17116 uu____17123);
          (match stack1 with
           | [] -> t
           | (Debug (tm,time_then))::stack2 ->
               ((let uu____17156 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____17156
                 then
                   let time_now = FStar_Util.now () in
                   let uu____17158 =
                     let uu____17159 =
                       let uu____17160 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____17160 in
                     FStar_Util.string_of_int uu____17159 in
                   let uu____17165 = FStar_Syntax_Print.term_to_string tm in
                   let uu____17166 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17158 uu____17165 uu____17166
                 else ());
                rebuild cfg env stack2 t)
           | (Steps (s,ps,dl))::stack2 ->
               rebuild
                 (let uu___240_17184 = cfg in
                  {
                    steps = s;
                    tcenv = (uu___240_17184.tcenv);
                    delta_level = dl;
                    primitive_steps = ps
                  }) env stack2 t
           | (Meta (m,r))::stack2 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack2 t1
           | (MemoLazy r)::stack2 ->
               (set_memo r (env, t);
                log cfg
                  (fun uu____17277  ->
                     let uu____17278 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17278);
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
               let uu____17314 =
                 let uu___241_17315 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___241_17315.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___241_17315.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack2 uu____17314
           | (Arg (Univ uu____17316,uu____17317,uu____17318))::uu____17319 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17322,uu____17323))::uu____17324 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack2 t1
           | (Arg (Clos (env_arg,tm,m,uu____17340),aq,r))::stack2 ->
               (log cfg
                  (fun uu____17393  ->
                     let uu____17394 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17394);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains WHNF cfg.steps
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
                  (let uu____17404 = FStar_ST.op_Bang m in
                   match uu____17404 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains WHNF cfg.steps
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
                   | FStar_Pervasives_Native.Some (uu____17548,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack2 t1))
           | (App (env1,head1,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17591 = maybe_simplify cfg env1 stack2 t1 in
               rebuild cfg env1 stack2 uu____17591
           | (Match (env1,branches,r))::stack2 ->
               (log cfg
                  (fun uu____17603  ->
                     let uu____17604 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17604);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17609 =
                   log cfg
                     (fun uu____17614  ->
                        let uu____17615 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17616 =
                          let uu____17617 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17634  ->
                                    match uu____17634 with
                                    | (p,uu____17644,uu____17645) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17617
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17615 uu____17616);
                   (let whnf1 = FStar_List.contains WHNF cfg.steps in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___183_17662  ->
                                match uu___183_17662 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17663 -> false)) in
                      let steps' =
                        let uu____17667 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____17667
                        then [Exclude Zeta]
                        else [Exclude Iota; Exclude Zeta] in
                      only_strong_steps
                        (let uu___242_17673 = cfg in
                         {
                           steps = (FStar_List.append steps' cfg.steps);
                           tcenv = (uu___242_17673.tcenv);
                           delta_level = new_delta;
                           primitive_steps = (uu___242_17673.primitive_steps)
                         }) in
                    let norm_or_whnf env2 t1 =
                      if whnf1
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17705 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17726 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17786  ->
                                    fun uu____17787  ->
                                      match (uu____17786, uu____17787) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17878 = norm_pat env3 p1 in
                                          (match uu____17878 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17726 with
                           | (pats1,env3) ->
                               ((let uu___243_17960 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___243_17960.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___244_17979 = x in
                            let uu____17980 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___244_17979.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___244_17979.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17980
                            } in
                          ((let uu___245_17994 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___245_17994.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___246_18005 = x in
                            let uu____18006 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___246_18005.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___246_18005.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18006
                            } in
                          ((let uu___247_18020 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___247_18020.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___248_18036 = x in
                            let uu____18037 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___248_18036.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___248_18036.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18037
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___249_18044 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___249_18044.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf1 -> branches
                      | uu____18054 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18068 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____18068 with
                                  | (p,wopt,e) ->
                                      let uu____18088 = norm_pat env1 p in
                                      (match uu____18088 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18113 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18113 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____18119 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack2 uu____18119) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18129) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18134 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18135;
                         FStar_Syntax_Syntax.fv_delta = uu____18136;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18137;
                         FStar_Syntax_Syntax.fv_delta = uu____18138;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18139);_}
                       -> true
                   | uu____18146 -> false in
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
                   let uu____18291 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____18291 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18378 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when 
                                 s = s' -> FStar_Util.Inl []
                             | uu____18417 ->
                                 let uu____18418 =
                                   let uu____18419 = is_cons head1 in
                                   Prims.op_Negation uu____18419 in
                                 FStar_Util.Inr uu____18418)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18444 =
                              let uu____18445 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____18445.FStar_Syntax_Syntax.n in
                            (match uu____18444 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18463 ->
                                 let uu____18464 =
                                   let uu____18465 = is_cons head1 in
                                   Prims.op_Negation uu____18465 in
                                 FStar_Util.Inr uu____18464))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18534)::rest_a,(p1,uu____18537)::rest_p) ->
                       let uu____18581 = matches_pat t1 p1 in
                       (match uu____18581 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18630 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18736 = matches_pat scrutinee1 p1 in
                       (match uu____18736 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18776  ->
                                  let uu____18777 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18778 =
                                    let uu____18779 =
                                      FStar_List.map
                                        (fun uu____18789  ->
                                           match uu____18789 with
                                           | (uu____18794,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18779
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18777 uu____18778);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18825  ->
                                       match uu____18825 with
                                       | (bv,t1) ->
                                           let uu____18848 =
                                             let uu____18855 =
                                               let uu____18858 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18858 in
                                             let uu____18859 =
                                               let uu____18860 =
                                                 let uu____18891 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18891, false) in
                                               Clos uu____18860 in
                                             (uu____18855, uu____18859) in
                                           uu____18848 :: env2) env1 s in
                              let uu____19000 = guard_when_clause wopt b rest in
                              norm cfg env2 stack2 uu____19000))) in
                 let uu____19001 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____19001
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___184_19024  ->
                match uu___184_19024 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____19028 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____19034 -> d in
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
            let uu___250_19063 = config s e in
            {
              steps = (uu___250_19063.steps);
              tcenv = (uu___250_19063.tcenv);
              delta_level = (uu___250_19063.delta_level);
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
      fun t  -> let uu____19094 = config s e in norm_comp uu____19094 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____19109 = config [] env in norm_universe uu____19109 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____19124 = config [] env in ghost_to_pure_aux uu____19124 [] c
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
        let uu____19144 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____19144 in
      let uu____19151 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____19151
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___251_19153 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___251_19153.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___251_19153.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____19156  ->
                    let uu____19157 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____19157))
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
            ((let uu____19176 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19176);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19189 = config [AllowUnboundUniverses] env in
          norm_comp uu____19189 [] c
        with
        | e ->
            ((let uu____19202 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning
                "Normalization failed with error %s\n" uu____19202);
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
                   let uu____19242 =
                     let uu____19243 =
                       let uu____19250 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____19250) in
                     FStar_Syntax_Syntax.Tm_refine uu____19243 in
                   mk uu____19242 t01.FStar_Syntax_Syntax.pos
               | uu____19255 -> t2)
          | uu____19256 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
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
        let uu____19308 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____19308 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____19337 ->
                 let uu____19344 = FStar_Syntax_Util.abs_formals e in
                 (match uu____19344 with
                  | (actuals,uu____19354,uu____19355) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____19369 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____19369 with
                         | (binders,args) ->
                             let uu____19386 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____19386
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
      | uu____19396 ->
          let uu____19397 = FStar_Syntax_Util.head_and_args t in
          (match uu____19397 with
           | (head1,args) ->
               let uu____19434 =
                 let uu____19435 = FStar_Syntax_Subst.compress head1 in
                 uu____19435.FStar_Syntax_Syntax.n in
               (match uu____19434 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19438,thead) ->
                    let uu____19464 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____19464 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19506 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___256_19514 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___256_19514.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___256_19514.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___256_19514.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___256_19514.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___256_19514.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___256_19514.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___256_19514.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___256_19514.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___256_19514.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___256_19514.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___256_19514.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___256_19514.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___256_19514.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___256_19514.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___256_19514.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___256_19514.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___256_19514.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___256_19514.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___256_19514.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___256_19514.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___256_19514.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___256_19514.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___256_19514.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___256_19514.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___256_19514.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___256_19514.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___256_19514.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___256_19514.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___256_19514.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___256_19514.FStar_TypeChecker_Env.dsenv)
                                 }) t in
                            match uu____19506 with
                            | (uu____19515,ty,uu____19517) ->
                                eta_expand_with_type env t ty))
                | uu____19518 ->
                    let uu____19519 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___257_19527 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___257_19527.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___257_19527.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___257_19527.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___257_19527.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___257_19527.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___257_19527.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___257_19527.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___257_19527.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___257_19527.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___257_19527.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___257_19527.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___257_19527.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___257_19527.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___257_19527.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___257_19527.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___257_19527.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___257_19527.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___257_19527.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___257_19527.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___257_19527.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___257_19527.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___257_19527.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___257_19527.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___257_19527.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___257_19527.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___257_19527.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___257_19527.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___257_19527.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___257_19527.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___257_19527.FStar_TypeChecker_Env.dsenv)
                         }) t in
                    (match uu____19519 with
                     | (uu____19528,ty,uu____19530) ->
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
            | (uu____19608,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19614,FStar_Util.Inl t) ->
                let uu____19620 =
                  let uu____19623 =
                    let uu____19624 =
                      let uu____19637 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19637) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19624 in
                  FStar_Syntax_Syntax.mk uu____19623 in
                uu____19620 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19641 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19641 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19668 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19723 ->
                    let uu____19724 =
                      let uu____19733 =
                        let uu____19734 = FStar_Syntax_Subst.compress t3 in
                        uu____19734.FStar_Syntax_Syntax.n in
                      (uu____19733, tc) in
                    (match uu____19724 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19759) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19796) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19835,FStar_Util.Inl uu____19836) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19859 -> failwith "Impossible") in
              (match uu____19668 with
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
          let uu____19968 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19968 with
          | (univ_names1,binders1,tc) ->
              let uu____20026 = FStar_Util.left tc in
              (univ_names1, binders1, uu____20026)
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
          let uu____20065 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20065 with
          | (univ_names1,binders1,tc) ->
              let uu____20125 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20125)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20160 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20160 with
           | (univ_names1,binders1,typ1) ->
               let uu___258_20188 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___258_20188.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___258_20188.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___258_20188.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___258_20188.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___259_20209 = s in
          let uu____20210 =
            let uu____20211 =
              let uu____20220 = FStar_List.map (elim_uvars env) sigs in
              (uu____20220, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20211 in
          {
            FStar_Syntax_Syntax.sigel = uu____20210;
            FStar_Syntax_Syntax.sigrng =
              (uu___259_20209.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___259_20209.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___259_20209.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___259_20209.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20237 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20237 with
           | (univ_names1,uu____20255,typ1) ->
               let uu___260_20269 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___260_20269.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___260_20269.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___260_20269.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___260_20269.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20275 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20275 with
           | (univ_names1,uu____20293,typ1) ->
               let uu___261_20307 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___261_20307.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___261_20307.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___261_20307.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___261_20307.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20341 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20341 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20364 =
                            let uu____20365 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____20365 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____20364 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___262_20368 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___262_20368.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___262_20368.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___263_20369 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___263_20369.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___263_20369.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___263_20369.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___263_20369.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___264_20381 = s in
          let uu____20382 =
            let uu____20383 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20383 in
          {
            FStar_Syntax_Syntax.sigel = uu____20382;
            FStar_Syntax_Syntax.sigrng =
              (uu___264_20381.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___264_20381.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___264_20381.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___264_20381.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20387 = elim_uvars_aux_t env us [] t in
          (match uu____20387 with
           | (us1,uu____20405,t1) ->
               let uu___265_20419 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___265_20419.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___265_20419.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___265_20419.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___265_20419.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20420 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20422 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20422 with
           | (univs1,binders,signature) ->
               let uu____20450 =
                 let uu____20459 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20459 with
                 | (univs_opening,univs2) ->
                     let uu____20486 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20486) in
               (match uu____20450 with
                | (univs_opening,univs_closing) ->
                    let uu____20503 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20509 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20510 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20509, uu____20510) in
                    (match uu____20503 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20532 =
                           match uu____20532 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20550 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20550 with
                                | (us1,t1) ->
                                    let uu____20561 =
                                      let uu____20566 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20573 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20566, uu____20573) in
                                    (match uu____20561 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20586 =
                                           let uu____20591 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20600 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20591, uu____20600) in
                                         (match uu____20586 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20616 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20616 in
                                              let uu____20617 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20617 with
                                               | (uu____20638,uu____20639,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20654 =
                                                       let uu____20655 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20655 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20654 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20660 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20660 with
                           | (uu____20673,uu____20674,t1) -> t1 in
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
                             | uu____20734 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20751 =
                               let uu____20752 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20752.FStar_Syntax_Syntax.n in
                             match uu____20751 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20811 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20840 =
                               let uu____20841 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20841.FStar_Syntax_Syntax.n in
                             match uu____20840 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20862) ->
                                 let uu____20883 = destruct_action_body body in
                                 (match uu____20883 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20928 ->
                                 let uu____20929 = destruct_action_body t in
                                 (match uu____20929 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20978 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20978 with
                           | (action_univs,t) ->
                               let uu____20987 = destruct_action_typ_templ t in
                               (match uu____20987 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___266_21028 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___266_21028.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___266_21028.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___267_21030 = ed in
                           let uu____21031 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____21032 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____21033 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21034 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21035 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21036 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21037 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21038 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21039 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21040 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21041 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21042 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21043 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21044 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___267_21030.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___267_21030.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____21031;
                             FStar_Syntax_Syntax.bind_wp = uu____21032;
                             FStar_Syntax_Syntax.if_then_else = uu____21033;
                             FStar_Syntax_Syntax.ite_wp = uu____21034;
                             FStar_Syntax_Syntax.stronger = uu____21035;
                             FStar_Syntax_Syntax.close_wp = uu____21036;
                             FStar_Syntax_Syntax.assert_p = uu____21037;
                             FStar_Syntax_Syntax.assume_p = uu____21038;
                             FStar_Syntax_Syntax.null_wp = uu____21039;
                             FStar_Syntax_Syntax.trivial = uu____21040;
                             FStar_Syntax_Syntax.repr = uu____21041;
                             FStar_Syntax_Syntax.return_repr = uu____21042;
                             FStar_Syntax_Syntax.bind_repr = uu____21043;
                             FStar_Syntax_Syntax.actions = uu____21044
                           } in
                         let uu___268_21047 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___268_21047.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___268_21047.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___268_21047.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___268_21047.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___185_21064 =
            match uu___185_21064 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21091 = elim_uvars_aux_t env us [] t in
                (match uu____21091 with
                 | (us1,uu____21115,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___269_21134 = sub_eff in
            let uu____21135 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21138 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___269_21134.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___269_21134.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21135;
              FStar_Syntax_Syntax.lift = uu____21138
            } in
          let uu___270_21141 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___270_21141.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___270_21141.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___270_21141.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___270_21141.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____21151 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21151 with
           | (univ_names1,binders1,comp1) ->
               let uu___271_21185 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___271_21185.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___271_21185.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___271_21185.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___271_21185.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21196 -> s