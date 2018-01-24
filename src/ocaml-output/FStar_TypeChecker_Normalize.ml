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
  | Unmeta [@@deriving show]
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____18 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____22 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____26 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____31 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____42 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____46 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____50 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____54 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____58 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____62 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____67 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____81 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____98 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____102 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____106 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____110 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____114 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____118 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____122 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____126 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____130 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____134 -> false
  
type steps = step Prims.list[@@deriving show]
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____168  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    }[@@deriving show]
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
  
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
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
  | Dummy [@@deriving show]
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____369 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____471 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____482 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___71_501  ->
    match uu___71_501 with
    | Clos (uu____502,t,uu____504,uu____505) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____550 -> "Univ"
    | Dummy  -> "dummy"
  
type cfg =
  {
  steps: steps ;
  tcenv: FStar_TypeChecker_Env.env ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step Prims.list ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool }[@@deriving show]
let (__proj__Mkcfg__item__steps : cfg -> steps) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__tcenv
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__delta_level
  
let (__proj__Mkcfg__item__primitive_steps : cfg -> primitive_step Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__memoize_lazy
  
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____816 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____852 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____888 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____957 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____999 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1055 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1095 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1127 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Steps : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____1173 -> false
  
let (__proj__Steps__item___0 :
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Steps _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1219 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____1244 .
    'Auu____1244 ->
      FStar_Range.range -> 'Auu____1244 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1298 = FStar_ST.op_Bang r  in
          match uu____1298 with
          | FStar_Pervasives_Native.Some uu____1346 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____1400 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____1400 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___72_1407  ->
    match uu___72_1407 with
    | Arg (c,uu____1409,uu____1410) ->
        let uu____1411 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1411
    | MemoLazy uu____1412 -> "MemoLazy"
    | Abs (uu____1419,bs,uu____1421,uu____1422,uu____1423) ->
        let uu____1428 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1428
    | UnivArgs uu____1433 -> "UnivArgs"
    | Match uu____1440 -> "Match"
    | App (uu____1447,t,uu____1449,uu____1450) ->
        let uu____1451 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1451
    | Meta (m,uu____1453) -> "Meta"
    | Let uu____1454 -> "Let"
    | Steps (uu____1463,uu____1464,uu____1465) -> "Steps"
    | Debug (t,uu____1475) ->
        let uu____1476 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1476
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1484 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1484 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1500 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____1500 then f () else ()
  
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1513 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops"))
         in
      if uu____1513 then f () else ()
  
let is_empty : 'Auu____1517 . 'Auu____1517 Prims.list -> Prims.bool =
  fun uu___73_1523  ->
    match uu___73_1523 with | [] -> true | uu____1526 -> false
  
let lookup_bvar :
  'Auu____1533 'Auu____1534 .
    ('Auu____1534,'Auu____1533) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1533
  =
  fun env  ->
    fun x  ->
      try
        let uu____1558 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____1558
      with
      | uu____1571 ->
          let uu____1572 =
            let uu____1573 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____1573  in
          failwith uu____1572
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
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
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____1610 =
            FStar_List.fold_left
              (fun uu____1636  ->
                 fun u1  ->
                   match uu____1636 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1661 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1661 with
                        | (k_u,n1) ->
                            let uu____1676 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1676
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1610 with
          | (uu____1694,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1719 =
                   let uu____1720 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____1720  in
                 match uu____1719 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1738 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1747 ->
                   let uu____1748 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____1748
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1754 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1763 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1772 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1779 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1779 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1796 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1796 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1804 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1812 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1812 with
                                  | (uu____1817,m) -> n1 <= m))
                           in
                        if uu____1804 then rest1 else us1
                    | uu____1822 -> us1)
               | uu____1827 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1831 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1831
           in
        let uu____1834 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____1834
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1836 = aux u  in
           match uu____1836 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____1940  ->
             let uu____1941 = FStar_Syntax_Print.tag_of_term t  in
             let uu____1942 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1941
               uu____1942);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1949 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1951 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1976 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1977 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1978 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1979 ->
                  let uu____1996 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars)
                     in
                  if uu____1996
                  then
                    let uu____1997 =
                      let uu____1998 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____1999 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1998 uu____1999
                       in
                    failwith uu____1997
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2002 =
                    let uu____2003 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____2003  in
                  mk uu____2002 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2010 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2010
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2012 = lookup_bvar env x  in
                  (match uu____2012 with
                   | Univ uu____2015 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____2018,uu____2019) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2131 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2131 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____2159 =
                         let uu____2160 =
                           let uu____2177 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____2177)  in
                         FStar_Syntax_Syntax.Tm_abs uu____2160  in
                       mk uu____2159 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2208 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2208 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2250 =
                    let uu____2261 =
                      let uu____2268 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____2268]  in
                    closures_as_binders_delayed cfg env uu____2261  in
                  (match uu____2250 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____2286 =
                         let uu____2287 =
                           let uu____2294 =
                             let uu____2295 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____2295
                               FStar_Pervasives_Native.fst
                              in
                           (uu____2294, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____2287  in
                       mk uu____2286 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2386 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____2386
                    | FStar_Util.Inr c ->
                        let uu____2400 = close_comp cfg env c  in
                        FStar_Util.Inr uu____2400
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____2416 =
                    let uu____2417 =
                      let uu____2444 = closure_as_term_delayed cfg env t11
                         in
                      (uu____2444, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2417  in
                  mk uu____2416 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2495 =
                    let uu____2496 =
                      let uu____2503 = closure_as_term_delayed cfg env t'  in
                      let uu____2506 =
                        let uu____2507 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____2507  in
                      (uu____2503, uu____2506)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2496  in
                  mk uu____2495 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2567 =
                    let uu____2568 =
                      let uu____2575 = closure_as_term_delayed cfg env t'  in
                      let uu____2578 =
                        let uu____2579 =
                          let uu____2586 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____2586)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____2579  in
                      (uu____2575, uu____2578)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2568  in
                  mk uu____2567 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2605 =
                    let uu____2606 =
                      let uu____2613 = closure_as_term_delayed cfg env t'  in
                      let uu____2616 =
                        let uu____2617 =
                          let uu____2626 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____2626)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2617  in
                      (uu____2613, uu____2616)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2606  in
                  mk uu____2605 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2639 =
                    let uu____2640 =
                      let uu____2647 = closure_as_term_delayed cfg env t'  in
                      (uu____2647, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2640  in
                  mk uu____2639 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2687  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____2706 =
                    let uu____2717 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____2717
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____2736 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___92_2748 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___92_2748.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___92_2748.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2736))
                     in
                  (match uu____2706 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___93_2764 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___93_2764.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___93_2764.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2775,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2834  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____2859 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____2859
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2879  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____2901 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____2901
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___94_2913 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___94_2913.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___94_2913.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___95_2914 = lb  in
                    let uu____2915 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___95_2914.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___95_2914.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2915
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2945  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____3034 =
                    match uu____3034 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3089 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3110 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3170  ->
                                        fun uu____3171  ->
                                          match (uu____3170, uu____3171) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3262 =
                                                norm_pat env3 p1  in
                                              (match uu____3262 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____3110 with
                               | (pats1,env3) ->
                                   ((let uu___96_3344 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___96_3344.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___97_3363 = x  in
                                let uu____3364 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___97_3363.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___97_3363.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3364
                                }  in
                              ((let uu___98_3378 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___98_3378.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___99_3389 = x  in
                                let uu____3390 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___99_3389.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___99_3389.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3390
                                }  in
                              ((let uu___100_3404 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___100_3404.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___101_3420 = x  in
                                let uu____3421 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___101_3420.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___101_3420.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3421
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___102_3428 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___102_3428.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____3431 = norm_pat env1 pat  in
                        (match uu____3431 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3460 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____3460
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____3466 =
                    let uu____3467 =
                      let uu____3490 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____3490)  in
                    FStar_Syntax_Syntax.Tm_match uu____3467  in
                  mk uu____3466 t1.FStar_Syntax_Syntax.pos))

and (closure_as_term_delayed :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____3576 -> closure_as_term cfg env t

and (closures_as_args_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____3602 ->
            FStar_List.map
              (fun uu____3619  ->
                 match uu____3619 with
                 | (x,imp) ->
                     let uu____3638 = closure_as_term_delayed cfg env x  in
                     (uu____3638, imp)) args

and (closures_as_binders_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____3652 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3701  ->
                  fun uu____3702  ->
                    match (uu____3701, uu____3702) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___103_3772 = b  in
                          let uu____3773 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___103_3772.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___103_3772.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3773
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____3652 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____3866 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3879 = closure_as_term_delayed cfg env t  in
                 let uu____3880 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____3879 uu____3880
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3893 = closure_as_term_delayed cfg env t  in
                 let uu____3894 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3893 uu____3894
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___74_3920  ->
                           match uu___74_3920 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3924 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____3924
                           | f -> f))
                    in
                 let uu____3928 =
                   let uu___104_3929 = c1  in
                   let uu____3930 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3930;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___104_3929.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____3928)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___75_3940  ->
            match uu___75_3940 with
            | FStar_Syntax_Syntax.DECREASES uu____3941 -> false
            | uu____3944 -> true))

and (close_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___76_3962  ->
                      match uu___76_3962 with
                      | FStar_Syntax_Syntax.DECREASES uu____3963 -> false
                      | uu____3966 -> true))
               in
            let rc1 =
              let uu___105_3968 = rc  in
              let uu____3969 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___105_3968.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3969;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____3976 -> lopt

let (built_in_primitive_steps : primitive_step Prims.list) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe
     in
  let arg_as_list u a =
    let uu____4066 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4066  in
  let arg_as_bounded_int uu____4094 =
    match uu____4094 with
    | (a,uu____4106) ->
        let uu____4113 =
          let uu____4114 = FStar_Syntax_Subst.compress a  in
          uu____4114.FStar_Syntax_Syntax.n  in
        (match uu____4113 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4124;
                FStar_Syntax_Syntax.vars = uu____4125;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4127;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4128;_},uu____4129)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4168 =
               let uu____4173 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____4173)  in
             FStar_Pervasives_Native.Some uu____4168
         | uu____4178 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4220 = f a  in FStar_Pervasives_Native.Some uu____4220
    | uu____4221 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4271 = f a0 a1  in FStar_Pervasives_Native.Some uu____4271
    | uu____4272 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____4321 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4321  in
  let binary_op as_a f res args =
    let uu____4377 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4377  in
  let as_primitive_step uu____4401 =
    match uu____4401 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  ->
         fun x  ->
           let uu____4449 = f x  in
           FStar_Syntax_Embeddings.embed_int r uu____4449)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4477 = f x y  in
             FStar_Syntax_Embeddings.embed_int r uu____4477)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4498 = f x  in
           FStar_Syntax_Embeddings.embed_bool r uu____4498)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4526 = f x y  in
             FStar_Syntax_Embeddings.embed_bool r uu____4526)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4554 = f x y  in
             FStar_Syntax_Embeddings.embed_string r uu____4554)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4671 =
          let uu____4680 = as_a a  in
          let uu____4683 = as_b b  in (uu____4680, uu____4683)  in
        (match uu____4671 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4698 =
               let uu____4699 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____4699  in
             FStar_Pervasives_Native.Some uu____4698
         | uu____4700 -> FStar_Pervasives_Native.None)
    | uu____4709 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____4723 =
        let uu____4724 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____4724  in
      mk uu____4723 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____4734 =
      let uu____4737 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____4737  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4734  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____4769 =
      let uu____4770 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____4770  in
    FStar_Syntax_Embeddings.embed_int rng uu____4769  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4788 = arg_as_string a1  in
        (match uu____4788 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4794 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2  in
             (match uu____4794 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4807 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____4807
              | uu____4808 -> FStar_Pervasives_Native.None)
         | uu____4813 -> FStar_Pervasives_Native.None)
    | uu____4816 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____4826 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____4826  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____4850 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4861 =
          let uu____4882 = arg_as_string fn  in
          let uu____4885 = arg_as_int from_line  in
          let uu____4888 = arg_as_int from_col  in
          let uu____4891 = arg_as_int to_line  in
          let uu____4894 = arg_as_int to_col  in
          (uu____4882, uu____4885, uu____4888, uu____4891, uu____4894)  in
        (match uu____4861 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4925 =
                 let uu____4926 = FStar_BigInt.to_int_fs from_l  in
                 let uu____4927 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____4926 uu____4927  in
               let uu____4928 =
                 let uu____4929 = FStar_BigInt.to_int_fs to_l  in
                 let uu____4930 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____4929 uu____4930  in
               FStar_Range.mk_range fn1 uu____4925 uu____4928  in
             let uu____4931 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____4931
         | uu____4936 -> FStar_Pervasives_Native.None)
    | uu____4957 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____4984)::(a1,uu____4986)::(a2,uu____4988)::[] ->
        let uu____5025 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____5025 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5038 -> FStar_Pervasives_Native.None)
    | uu____5039 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____5066)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5075 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____5099 =
      let uu____5114 =
        let uu____5129 =
          let uu____5144 =
            let uu____5159 =
              let uu____5174 =
                let uu____5189 =
                  let uu____5204 =
                    let uu____5219 =
                      let uu____5234 =
                        let uu____5249 =
                          let uu____5264 =
                            let uu____5279 =
                              let uu____5294 =
                                let uu____5309 =
                                  let uu____5324 =
                                    let uu____5339 =
                                      let uu____5354 =
                                        let uu____5369 =
                                          let uu____5384 =
                                            let uu____5399 =
                                              let uu____5412 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"]
                                                 in
                                              (uu____5412,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string'))
                                               in
                                            let uu____5419 =
                                              let uu____5434 =
                                                let uu____5447 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"]
                                                   in
                                                (uu____5447,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list
                                                        FStar_Syntax_Embeddings.unembed_char_safe)
                                                     string_of_list'))
                                                 in
                                              let uu____5458 =
                                                let uu____5473 =
                                                  let uu____5488 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"]
                                                     in
                                                  (uu____5488,
                                                    (Prims.parse_int "2"),
                                                    string_concat')
                                                   in
                                                let uu____5497 =
                                                  let uu____5514 =
                                                    let uu____5529 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "mk_range"]
                                                       in
                                                    (uu____5529,
                                                      (Prims.parse_int "5"),
                                                      mk_range1)
                                                     in
                                                  let uu____5538 =
                                                    let uu____5555 =
                                                      let uu____5574 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "Range";
                                                          "prims_to_fstar_range"]
                                                         in
                                                      (uu____5574,
                                                        (Prims.parse_int "1"),
                                                        idstep)
                                                       in
                                                    [uu____5555]  in
                                                  uu____5514 :: uu____5538
                                                   in
                                                uu____5473 :: uu____5497  in
                                              uu____5434 :: uu____5458  in
                                            uu____5399 :: uu____5419  in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5384
                                           in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5369
                                         in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5354
                                       in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool1))
                                      :: uu____5339
                                     in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int1)) ::
                                    uu____5324
                                   in
                                (FStar_Parser_Const.str_make_lid,
                                  (Prims.parse_int "2"),
                                  (mixed_binary_op arg_as_int arg_as_char
                                     FStar_Syntax_Embeddings.embed_string
                                     (fun r  ->
                                        fun x  ->
                                          fun y  ->
                                            let uu____5792 =
                                              FStar_BigInt.to_int_fs x  in
                                            FStar_String.make uu____5792 y)))
                                  :: uu____5309
                                 in
                              (FStar_Parser_Const.strcat_lid',
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5294
                               in
                            (FStar_Parser_Const.strcat_lid,
                              (Prims.parse_int "2"),
                              (binary_string_op
                                 (fun x  -> fun y  -> Prims.strcat x y)))
                              :: uu____5279
                             in
                          (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x || y))) ::
                            uu____5264
                           in
                        (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                          (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                          uu____5249
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5234
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5938 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed_bool r
                                  uu____5938)))
                      :: uu____5219
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5964 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed_bool r uu____5964)))
                    :: uu____5204
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5990 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed_bool r uu____5990)))
                  :: uu____5189
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____6016 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed_bool r uu____6016)))
                :: uu____5174
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5159
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5144
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5129
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5114
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5099
     in
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
      "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____6166 =
        let uu____6167 =
          let uu____6168 = FStar_Syntax_Syntax.as_arg c  in [uu____6168]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6167  in
      uu____6166 FStar_Pervasives_Native.None r  in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6203 =
              let uu____6216 = FStar_Parser_Const.p2l ["FStar"; m; "add"]  in
              (uu____6216, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6236  ->
                        fun uu____6237  ->
                          match (uu____6236, uu____6237) with
                          | ((int_to_t1,x),(uu____6256,y)) ->
                              let uu____6266 = FStar_BigInt.add_big_int x y
                                 in
                              int_as_bounded r int_to_t1 uu____6266)))
               in
            let uu____6267 =
              let uu____6282 =
                let uu____6295 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                   in
                (uu____6295, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6315  ->
                          fun uu____6316  ->
                            match (uu____6315, uu____6316) with
                            | ((int_to_t1,x),(uu____6335,y)) ->
                                let uu____6345 = FStar_BigInt.sub_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____6345)))
                 in
              let uu____6346 =
                let uu____6361 =
                  let uu____6374 = FStar_Parser_Const.p2l ["FStar"; m; "mul"]
                     in
                  (uu____6374, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6394  ->
                            fun uu____6395  ->
                              match (uu____6394, uu____6395) with
                              | ((int_to_t1,x),(uu____6414,y)) ->
                                  let uu____6424 =
                                    FStar_BigInt.mult_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____6424)))
                   in
                [uu____6361]  in
              uu____6282 :: uu____6346  in
            uu____6203 :: uu____6267))
     in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
  
let (equality_ops : primitive_step Prims.list) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____6514)::(a1,uu____6516)::(a2,uu____6518)::[] ->
        let uu____6555 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6555 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6561 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6561.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6561.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6565 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6565.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6565.FStar_Syntax_Syntax.vars)
                })
         | uu____6566 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6568)::uu____6569::(a1,uu____6571)::(a2,uu____6573)::[] ->
        let uu____6622 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6622 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___106_6628 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___106_6628.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___106_6628.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6632 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6632.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6632.FStar_Syntax_Syntax.vars)
                })
         | uu____6633 -> FStar_Pervasives_Native.None)
    | uu____6634 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  [propositional_equality; hetero_propositional_equality] 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____6653 =
        let uu____6654 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____6654 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____6653
    with | uu____6660 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____6664 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6664) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6724  ->
           fun subst1  ->
             match uu____6724 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6765,uu____6766)) ->
                      let uu____6825 = b  in
                      (match uu____6825 with
                       | (bv,uu____6833) ->
                           let uu____6834 =
                             let uu____6835 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____6835  in
                           if uu____6834
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____6840 = unembed_binder term1  in
                              match uu____6840 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6847 =
                                      let uu___110_6848 = bv  in
                                      let uu____6849 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___110_6848.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___110_6848.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6849
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____6847
                                     in
                                  let b_for_x =
                                    let uu____6853 =
                                      let uu____6860 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6860)
                                       in
                                    FStar_Syntax_Syntax.NT uu____6853  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___77_6869  ->
                                         match uu___77_6869 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6870,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6872;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6873;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6878 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____6879 -> subst1)) env []
  
let reduce_primops :
  'Auu____6896 'Auu____6897 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6897) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6896 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6938 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps)
             in
          if uu____6938
          then tm
          else
            (let uu____6940 = FStar_Syntax_Util.head_and_args tm  in
             match uu____6940 with
             | (head1,args) ->
                 let uu____6977 =
                   let uu____6978 = FStar_Syntax_Util.un_uinst head1  in
                   uu____6978.FStar_Syntax_Syntax.n  in
                 (match uu____6977 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6982 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps
                         in
                      (match uu____6982 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6999  ->
                                   let uu____7000 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____7001 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____7008 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7000 uu____7001 uu____7008);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7013  ->
                                   let uu____7014 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7014);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7017  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____7019 =
                                 prim_step.interpretation psc args  in
                               match uu____7019 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7025  ->
                                         let uu____7026 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7026);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7032  ->
                                         let uu____7033 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____7034 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7033 uu____7034);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7035 ->
                           (log_primops cfg
                              (fun uu____7039  ->
                                 let uu____7040 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7040);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7044  ->
                            let uu____7045 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7045);
                       (match args with
                        | (a1,uu____7047)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7064 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7076  ->
                            let uu____7077 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7077);
                       (match args with
                        | (a1,uu____7079)::(a2,uu____7081)::[] ->
                            let uu____7108 =
                              FStar_Syntax_Embeddings.unembed_range a2  in
                            (match uu____7108 with
                             | FStar_Pervasives_Native.Some r ->
                                 let uu___111_7112 = a1  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___111_7112.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = r;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___111_7112.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7115 -> tm))
                  | uu____7124 -> tm))
  
let reduce_equality :
  'Auu____7129 'Auu____7130 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7130) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7129 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___112_7168 = cfg  in
         {
           steps = [Primops];
           tcenv = (uu___112_7168.tcenv);
           delta_level = (uu___112_7168.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___112_7168.strong);
           memoize_lazy = (uu___112_7168.memoize_lazy)
         }) tm
  
let maybe_simplify_aux :
  'Auu____7175 'Auu____7176 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7176) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7175 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____7218 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps)
             in
          if uu____7218
          then tm1
          else
            (let w t =
               let uu___113_7230 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___113_7230.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___113_7230.FStar_Syntax_Syntax.vars)
               }  in
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
               | uu____7247 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____7252 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____7252
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7273 =
                 match uu____7273 with
                 | (t1,q) ->
                     let uu____7286 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____7286 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7314 -> (t1, q))
                  in
               let uu____7323 = FStar_Syntax_Util.head_and_args t  in
               match uu____7323 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg)  in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7420;
                         FStar_Syntax_Syntax.vars = uu____7421;_},uu____7422);
                    FStar_Syntax_Syntax.pos = uu____7423;
                    FStar_Syntax_Syntax.vars = uu____7424;_},args)
                 ->
                 let uu____7450 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____7450
                 then
                   let uu____7451 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____7451 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7506)::
                        (uu____7507,(arg,uu____7509))::[] ->
                        maybe_auto_squash arg
                    | (uu____7574,(arg,uu____7576))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7577)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7642)::uu____7643::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7706::(FStar_Pervasives_Native.Some (false
                                   ),uu____7707)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7770 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7786 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____7786
                    then
                      let uu____7787 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____7787 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7842)::uu____7843::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7906::(FStar_Pervasives_Native.Some (true
                                     ),uu____7907)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7970)::
                          (uu____7971,(arg,uu____7973))::[] ->
                          maybe_auto_squash arg
                      | (uu____8038,(arg,uu____8040))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8041)::[]
                          -> maybe_auto_squash arg
                      | uu____8106 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8122 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____8122
                       then
                         let uu____8123 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____8123 with
                         | uu____8178::(FStar_Pervasives_Native.Some (true
                                        ),uu____8179)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8242)::uu____8243::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8306)::
                             (uu____8307,(arg,uu____8309))::[] ->
                             maybe_auto_squash arg
                         | (uu____8374,(p,uu____8376))::(uu____8377,(q,uu____8379))::[]
                             ->
                             let uu____8444 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____8444
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8446 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8462 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____8462
                          then
                            let uu____8463 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____8463 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8518)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8557)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8596 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8612 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____8612
                             then
                               match args with
                               | (t,uu____8614)::[] ->
                                   let uu____8631 =
                                     let uu____8632 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____8632.FStar_Syntax_Syntax.n  in
                                   (match uu____8631 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8635::[],body,uu____8637) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8664 -> tm1)
                                    | uu____8667 -> tm1)
                               | (uu____8668,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8669))::
                                   (t,uu____8671)::[] ->
                                   let uu____8710 =
                                     let uu____8711 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____8711.FStar_Syntax_Syntax.n  in
                                   (match uu____8710 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8714::[],body,uu____8716) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8743 -> tm1)
                                    | uu____8746 -> tm1)
                               | uu____8747 -> tm1
                             else
                               (let uu____8757 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____8757
                                then
                                  match args with
                                  | (t,uu____8759)::[] ->
                                      let uu____8776 =
                                        let uu____8777 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____8777.FStar_Syntax_Syntax.n  in
                                      (match uu____8776 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8780::[],body,uu____8782)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8809 -> tm1)
                                       | uu____8812 -> tm1)
                                  | (uu____8813,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8814))::(t,uu____8816)::[] ->
                                      let uu____8855 =
                                        let uu____8856 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____8856.FStar_Syntax_Syntax.n  in
                                      (match uu____8855 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8859::[],body,uu____8861)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8888 -> tm1)
                                       | uu____8891 -> tm1)
                                  | uu____8892 -> tm1
                                else
                                  (let uu____8902 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____8902
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8903;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8904;_},uu____8905)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8922;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8923;_},uu____8924)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8941 -> tm1
                                   else
                                     (let uu____8951 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____8951 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8971 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8981;
                    FStar_Syntax_Syntax.vars = uu____8982;_},args)
                 ->
                 let uu____9004 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____9004
                 then
                   let uu____9005 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____9005 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9060)::
                        (uu____9061,(arg,uu____9063))::[] ->
                        maybe_auto_squash arg
                    | (uu____9128,(arg,uu____9130))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9131)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9196)::uu____9197::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9260::(FStar_Pervasives_Native.Some (false
                                   ),uu____9261)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9324 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9340 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9340
                    then
                      let uu____9341 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9341 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9396)::uu____9397::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9460::(FStar_Pervasives_Native.Some (true
                                     ),uu____9461)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9524)::
                          (uu____9525,(arg,uu____9527))::[] ->
                          maybe_auto_squash arg
                      | (uu____9592,(arg,uu____9594))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9595)::[]
                          -> maybe_auto_squash arg
                      | uu____9660 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9676 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9676
                       then
                         let uu____9677 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9677 with
                         | uu____9732::(FStar_Pervasives_Native.Some (true
                                        ),uu____9733)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9796)::uu____9797::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9860)::
                             (uu____9861,(arg,uu____9863))::[] ->
                             maybe_auto_squash arg
                         | (uu____9928,(p,uu____9930))::(uu____9931,(q,uu____9933))::[]
                             ->
                             let uu____9998 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9998
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10000 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10016 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____10016
                          then
                            let uu____10017 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____10017 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10072)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10111)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10150 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10166 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____10166
                             then
                               match args with
                               | (t,uu____10168)::[] ->
                                   let uu____10185 =
                                     let uu____10186 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10186.FStar_Syntax_Syntax.n  in
                                   (match uu____10185 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10189::[],body,uu____10191) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10218 -> tm1)
                                    | uu____10221 -> tm1)
                               | (uu____10222,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10223))::
                                   (t,uu____10225)::[] ->
                                   let uu____10264 =
                                     let uu____10265 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10265.FStar_Syntax_Syntax.n  in
                                   (match uu____10264 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10268::[],body,uu____10270) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10297 -> tm1)
                                    | uu____10300 -> tm1)
                               | uu____10301 -> tm1
                             else
                               (let uu____10311 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10311
                                then
                                  match args with
                                  | (t,uu____10313)::[] ->
                                      let uu____10330 =
                                        let uu____10331 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10331.FStar_Syntax_Syntax.n  in
                                      (match uu____10330 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10334::[],body,uu____10336)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10363 -> tm1)
                                       | uu____10366 -> tm1)
                                  | (uu____10367,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10368))::(t,uu____10370)::[] ->
                                      let uu____10409 =
                                        let uu____10410 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10410.FStar_Syntax_Syntax.n  in
                                      (match uu____10409 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10413::[],body,uu____10415)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10442 -> tm1)
                                       | uu____10445 -> tm1)
                                  | uu____10446 -> tm1
                                else
                                  (let uu____10456 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10456
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10457;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10458;_},uu____10459)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10476;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10477;_},uu____10478)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10495 -> tm1
                                   else
                                     (let uu____10505 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10505 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10525 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10534 -> tm1)
  
let maybe_simplify :
  'Auu____10541 'Auu____10542 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10542) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10541 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          (let uu____10585 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380")
              in
           if uu____10585
           then
             let uu____10586 = FStar_Syntax_Print.term_to_string tm  in
             let uu____10587 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10586 uu____10587
           else ());
          tm'
  
let is_norm_request :
  'Auu____10593 .
    FStar_Syntax_Syntax.term -> 'Auu____10593 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10606 =
        let uu____10613 =
          let uu____10614 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10614.FStar_Syntax_Syntax.n  in
        (uu____10613, args)  in
      match uu____10606 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10620::uu____10621::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10625::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10630::uu____10631::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10634 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___78_10645  ->
    match uu___78_10645 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10651 =
          let uu____10654 =
            let uu____10655 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10655  in
          [uu____10654]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10651
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10670 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10670) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10708 =
          let uu____10711 =
            let uu____10716 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step
               in
            uu____10716 s  in
          FStar_All.pipe_right uu____10711 FStar_Util.must  in
        FStar_All.pipe_right uu____10708 tr_norm_steps  in
      match args with
      | uu____10741::(tm,uu____10743)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____10766)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____10781)::uu____10782::(tm,uu____10784)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
            let uu____10824 =
              let uu____10827 = full_norm steps  in parse_steps uu____10827
               in
            Beta :: uu____10824  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____10836 -> failwith "Impossible"
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___79_10853  ->
    match uu___79_10853 with
    | (App
        (uu____10856,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10857;
                       FStar_Syntax_Syntax.vars = uu____10858;_},uu____10859,uu____10860))::uu____10861
        -> true
    | uu____10868 -> false
  
let firstn :
  'Auu____10874 .
    Prims.int ->
      'Auu____10874 Prims.list ->
        ('Auu____10874 Prims.list,'Auu____10874 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify : cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____10910,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10911;
                         FStar_Syntax_Syntax.vars = uu____10912;_},uu____10913,uu____10914))::uu____10915
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10922 -> false
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11030  ->
               let uu____11031 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11032 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11033 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11040 =
                 let uu____11041 =
                   let uu____11044 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11044
                    in
                 stack_to_string uu____11041  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11031 uu____11032 uu____11033 uu____11040);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11067 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11092 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11109 =
                 let uu____11110 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos  in
                 let uu____11111 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11110 uu____11111
                  in
               failwith uu____11109
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11112 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11129 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11130 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11131;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11132;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11135;
                 FStar_Syntax_Syntax.fv_delta = uu____11136;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11137;
                 FStar_Syntax_Syntax.fv_delta = uu____11138;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11139);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11147 = FStar_Syntax_Syntax.lid_of_fv fv  in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11147 ->
               let b = should_reify cfg stack  in
               (log cfg
                  (fun uu____11153  ->
                     let uu____11154 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____11155 = FStar_Util.string_of_bool b  in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11154 uu____11155);
                if b
                then
                  (let uu____11156 = FStar_List.tl stack  in
                   do_unfold_fv cfg env uu____11156 t1 fv)
                else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args  in
               let hd2 = closure_as_term cfg env hd1  in
               let t2 =
                 let uu___114_11195 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___114_11195.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_11195.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11228 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____11228) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___115_11236 = cfg  in
                 let uu____11237 =
                   FStar_List.filter
                     (fun uu___80_11240  ->
                        match uu___80_11240 with
                        | UnfoldOnly uu____11241 -> false
                        | NoDeltaSteps  -> false
                        | uu____11244 -> true) cfg.steps
                    in
                 {
                   steps = uu____11237;
                   tcenv = (uu___115_11236.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___115_11236.primitive_steps);
                   strong = (uu___115_11236.strong);
                   memoize_lazy = (uu___115_11236.memoize_lazy)
                 }  in
               let uu____11245 = get_norm_request (norm cfg' env []) args  in
               (match uu____11245 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11261 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___81_11266  ->
                                match uu___81_11266 with
                                | UnfoldUntil uu____11267 -> true
                                | UnfoldOnly uu____11268 -> true
                                | uu____11271 -> false))
                         in
                      if uu____11261
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___116_11276 = cfg  in
                      {
                        steps = s;
                        tcenv = (uu___116_11276.tcenv);
                        delta_level;
                        primitive_steps = (uu___116_11276.primitive_steps);
                        strong = (uu___116_11276.strong);
                        memoize_lazy = (uu___116_11276.memoize_lazy)
                      }  in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack  in
                      let uu____11287 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms")
                         in
                      if uu____11287
                      then
                        let uu____11290 =
                          let uu____11291 =
                            let uu____11296 = FStar_Util.now ()  in
                            (t1, uu____11296)  in
                          Debug uu____11291  in
                        uu____11290 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of );
                  FStar_Syntax_Syntax.pos = uu____11298;
                  FStar_Syntax_Syntax.vars = uu____11299;_},a1::a2::rest)
               ->
               let uu____11347 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11347 with
                | (hd1,uu____11363) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    norm cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11428;
                  FStar_Syntax_Syntax.vars = uu____11429;_},a1::a2::rest)
               ->
               let uu____11477 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11477 with
                | (hd1,uu____11493) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    norm cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of );
                  FStar_Syntax_Syntax.pos = uu____11558;
                  FStar_Syntax_Syntax.vars = uu____11559;_},a1::a2::a3::rest)
               ->
               let uu____11620 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11620 with
                | (hd1,uu____11636) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1; a2]))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a3 :: rest)))
                        FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    norm cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____11707);
                  FStar_Syntax_Syntax.pos = uu____11708;
                  FStar_Syntax_Syntax.vars = uu____11709;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack)
               ->
               let uu____11741 = FStar_List.tl stack  in
               norm cfg env uu____11741 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11744;
                  FStar_Syntax_Syntax.vars = uu____11745;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11777 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11777 with
                | (reify_head,uu____11793) ->
                    let a1 =
                      let uu____11815 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a)
                         in
                      FStar_Syntax_Subst.compress uu____11815  in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11818);
                            FStar_Syntax_Syntax.pos = uu____11819;
                            FStar_Syntax_Syntax.vars = uu____11820;_},a2::[])
                         ->
                         norm cfg env stack (FStar_Pervasives_Native.fst a2)
                     | uu____11854 ->
                         let stack1 =
                           (App
                              (env, reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack  in
                         norm cfg env stack1 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11864 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11864
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11871 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____11871
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11874 =
                      let uu____11881 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11881, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11874  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___82_11894  ->
                         match uu___82_11894 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l))
                  in
               let should_delta1 =
                 let uu____11897 =
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
                           FStar_Parser_Const.false_lid))
                    in
                 if uu____11897
                 then false
                 else
                   (let uu____11899 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___83_11906  ->
                              match uu___83_11906 with
                              | UnfoldOnly uu____11907 -> true
                              | uu____11910 -> false))
                       in
                    match uu____11899 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11914 -> should_delta)
                  in
               (log cfg
                  (fun uu____11922  ->
                     let uu____11923 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____11924 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos
                        in
                     let uu____11925 =
                       FStar_Util.string_of_bool should_delta1  in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11923 uu____11924 uu____11925);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11928 = lookup_bvar env x  in
               (match uu____11928 with
                | Univ uu____11931 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11980 = FStar_ST.op_Bang r  in
                      (match uu____11980 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12098  ->
                                 let uu____12099 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12100 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12099
                                   uu____12100);
                            (let uu____12101 =
                               let uu____12102 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____12102.FStar_Syntax_Syntax.n  in
                             match uu____12101 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12105 ->
                                 norm cfg env2 stack t'
                             | uu____12122 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12192)::uu____12193 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12202)::uu____12203 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12213,uu____12214))::stack_rest ->
                    (match c with
                     | Univ uu____12218 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12227 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12248  ->
                                    let uu____12249 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12249);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12289  ->
                                    let uu____12290 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12290);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack1 ->
                    norm
                      (let uu___117_12340 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___117_12340.tcenv);
                         delta_level = dl;
                         primitive_steps = ps;
                         strong = (uu___117_12340.strong);
                         memoize_lazy = (uu___117_12340.memoize_lazy)
                       }) env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____12381  ->
                          let uu____12382 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12382);
                     norm cfg env stack1 t1)
                | (Debug uu____12383)::uu____12384 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12391 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12391
                    else
                      (let uu____12393 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12393 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12435  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12463 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12463
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12473 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12473)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12478 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12478.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12478.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12479 -> lopt  in
                           (log cfg
                              (fun uu____12485  ->
                                 let uu____12486 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12486);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack  in
                             let cfg1 =
                               let uu___119_12499 = cfg  in
                               {
                                 steps = (uu___119_12499.steps);
                                 tcenv = (uu___119_12499.tcenv);
                                 delta_level = (uu___119_12499.delta_level);
                                 primitive_steps =
                                   (uu___119_12499.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12499.memoize_lazy)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12510)::uu____12511 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12518 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12518
                    else
                      (let uu____12520 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12520 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12562  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12590 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12590
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12600 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12600)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12605 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12605.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12605.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12606 -> lopt  in
                           (log cfg
                              (fun uu____12612  ->
                                 let uu____12613 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12613);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack  in
                             let cfg1 =
                               let uu___119_12626 = cfg  in
                               {
                                 steps = (uu___119_12626.steps);
                                 tcenv = (uu___119_12626.tcenv);
                                 delta_level = (uu___119_12626.delta_level);
                                 primitive_steps =
                                   (uu___119_12626.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12626.memoize_lazy)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12637)::uu____12638 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12649 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12649
                    else
                      (let uu____12651 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12651 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12693  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12721 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12721
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12731 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12731)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12736 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12736.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12736.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12737 -> lopt  in
                           (log cfg
                              (fun uu____12743  ->
                                 let uu____12744 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12744);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack  in
                             let cfg1 =
                               let uu___119_12757 = cfg  in
                               {
                                 steps = (uu___119_12757.steps);
                                 tcenv = (uu___119_12757.tcenv);
                                 delta_level = (uu___119_12757.delta_level);
                                 primitive_steps =
                                   (uu___119_12757.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12757.memoize_lazy)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12768)::uu____12769 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12780 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12780
                    else
                      (let uu____12782 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12782 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12824  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12852 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12852
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12862 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12862)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12867 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12867.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12867.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12868 -> lopt  in
                           (log cfg
                              (fun uu____12874  ->
                                 let uu____12875 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12875);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack  in
                             let cfg1 =
                               let uu___119_12888 = cfg  in
                               {
                                 steps = (uu___119_12888.steps);
                                 tcenv = (uu___119_12888.tcenv);
                                 delta_level = (uu___119_12888.delta_level);
                                 primitive_steps =
                                   (uu___119_12888.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12888.memoize_lazy)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12899)::uu____12900 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12915 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12915
                    else
                      (let uu____12917 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12917 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12959  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12987 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12987
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12997 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12997)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_13002 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_13002.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_13002.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13003 -> lopt  in
                           (log cfg
                              (fun uu____13009  ->
                                 let uu____13010 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13010);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack  in
                             let cfg1 =
                               let uu___119_13023 = cfg  in
                               {
                                 steps = (uu___119_13023.steps);
                                 tcenv = (uu___119_13023.tcenv);
                                 delta_level = (uu___119_13023.delta_level);
                                 primitive_steps =
                                   (uu___119_13023.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_13023.memoize_lazy)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13034 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13034
                    else
                      (let uu____13036 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13036 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13078  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13106 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____13106
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13116 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13116)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_13121 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_13121.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_13121.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13122 -> lopt  in
                           (log cfg
                              (fun uu____13128  ->
                                 let uu____13129 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13129);
                            (let stack1 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack  in
                             let cfg1 =
                               let uu___119_13142 = cfg  in
                               {
                                 steps = (uu___119_13142.steps);
                                 tcenv = (uu___119_13142.tcenv);
                                 delta_level = (uu___119_13142.delta_level);
                                 primitive_steps =
                                   (uu___119_13142.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_13142.memoize_lazy)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____13191  ->
                         fun stack1  ->
                           match uu____13191 with
                           | (a,aq) ->
                               let uu____13203 =
                                 let uu____13204 =
                                   let uu____13211 =
                                     let uu____13212 =
                                       let uu____13243 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13243, false)  in
                                     Clos uu____13212  in
                                   (uu____13211, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13204  in
                               uu____13203 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13327  ->
                     let uu____13328 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13328);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains Weak cfg.steps
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___120_13364 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_13364.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_13364.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13365 ->
                      let uu____13370 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13370)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13373 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13373 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13404 =
                          let uu____13405 =
                            let uu____13412 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___121_13414 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_13414.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_13414.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13412)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13405  in
                        mk uu____13404 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13433 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13433
               else
                 (let uu____13435 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13435 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13443 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13467  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13443 c1  in
                      let t2 =
                        let uu____13489 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13489 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13548)::uu____13549 ->
                    (log cfg
                       (fun uu____13560  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13561)::uu____13562 ->
                    (log cfg
                       (fun uu____13573  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13574,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13575;
                                   FStar_Syntax_Syntax.vars = uu____13576;_},uu____13577,uu____13578))::uu____13579
                    ->
                    (log cfg
                       (fun uu____13588  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13589)::uu____13590 ->
                    (log cfg
                       (fun uu____13601  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13602 ->
                    (log cfg
                       (fun uu____13605  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13609  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13626 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13626
                         | FStar_Util.Inr c ->
                             let uu____13634 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13634
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Steps (s,ps,dl))::stack1 ->
                           let t2 =
                             let uu____13657 =
                               let uu____13658 =
                                 let uu____13685 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13685, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13658
                                in
                             mk uu____13657 t1.FStar_Syntax_Syntax.pos  in
                           norm
                             (let uu___122_13706 = cfg  in
                              {
                                steps = s;
                                tcenv = (uu___122_13706.tcenv);
                                delta_level = dl;
                                primitive_steps = ps;
                                strong = (uu___122_13706.strong);
                                memoize_lazy = (uu___122_13706.memoize_lazy)
                              }) env stack1 t2
                       | uu____13707 ->
                           let uu____13708 =
                             let uu____13709 =
                               let uu____13710 =
                                 let uu____13737 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13737, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13710
                                in
                             mk uu____13709 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____13708))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (FStar_List.contains CompressUvars cfg.steps)
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____13847 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13847 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___123_13867 = cfg  in
                               let uu____13868 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___123_13867.steps);
                                 tcenv = uu____13868;
                                 delta_level = (uu___123_13867.delta_level);
                                 primitive_steps =
                                   (uu___123_13867.primitive_steps);
                                 strong = (uu___123_13867.strong);
                                 memoize_lazy = (uu___123_13867.memoize_lazy)
                               }  in
                             let norm1 t2 =
                               let uu____13873 =
                                 let uu____13874 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13874  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13873
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___124_13877 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___124_13877.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___124_13877.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             }))
                  in
               let uu____13878 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13878
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13889,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13890;
                               FStar_Syntax_Syntax.lbunivs = uu____13891;
                               FStar_Syntax_Syntax.lbtyp = uu____13892;
                               FStar_Syntax_Syntax.lbeff = uu____13893;
                               FStar_Syntax_Syntax.lbdef = uu____13894;_}::uu____13895),uu____13896)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____13932 =
                 (let uu____13935 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____13935) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13937 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)
                             in
                          Prims.op_Negation uu____13937)))
                  in
               if uu____13932
               then
                 let binder =
                   let uu____13939 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13939  in
                 let env1 =
                   let uu____13949 =
                     let uu____13956 =
                       let uu____13957 =
                         let uu____13988 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13988,
                           false)
                          in
                       Clos uu____13957  in
                     ((FStar_Pervasives_Native.Some binder), uu____13956)  in
                   uu____13949 :: env  in
                 (log cfg
                    (fun uu____14081  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____14083 =
                    let uu____14088 =
                      let uu____14089 =
                        let uu____14090 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left
                           in
                        FStar_All.pipe_right uu____14090
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [uu____14089]  in
                    FStar_Syntax_Subst.open_term uu____14088 body  in
                  match uu____14083 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____14099  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let lbname =
                          let x =
                            let uu____14107 = FStar_List.hd bs  in
                            FStar_Pervasives_Native.fst uu____14107  in
                          FStar_Util.Inl
                            (let uu___125_14117 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___125_14117.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___125_14117.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             })
                           in
                        log cfg
                          (fun uu____14120  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___126_14122 = lb  in
                           let uu____14123 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___126_14122.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___126_14122.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____14123
                           }  in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____14158  -> dummy :: env1) env)
                            in
                         let cfg1 =
                           let uu___127_14178 = cfg  in
                           {
                             steps = (uu___127_14178.steps);
                             tcenv = (uu___127_14178.tcenv);
                             delta_level = (uu___127_14178.delta_level);
                             primitive_steps =
                               (uu___127_14178.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___127_14178.memoize_lazy)
                           }  in
                         log cfg1
                           (fun uu____14181  ->
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
               let uu____14198 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14198 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14234 =
                               let uu___128_14235 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___128_14235.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___128_14235.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14234  in
                           let uu____14236 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14236 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14262 =
                                   FStar_List.map (fun uu____14278  -> dummy)
                                     lbs1
                                    in
                                 let uu____14279 =
                                   let uu____14288 =
                                     FStar_List.map
                                       (fun uu____14308  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14288 env  in
                                 FStar_List.append uu____14262 uu____14279
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14332 =
                                       let uu___129_14333 = rc  in
                                       let uu____14334 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___129_14333.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14334;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___129_14333.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14332
                                 | uu____14341 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___130_14345 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___130_14345.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___130_14345.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
                      let uu____14355 =
                        FStar_List.map (fun uu____14371  -> dummy) lbs2  in
                      FStar_List.append uu____14355 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14379 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14379 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___131_14395 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___131_14395.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___131_14395.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14422 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14422
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14441 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14517  ->
                        match uu____14517 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___132_14638 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___132_14638.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___132_14638.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____14441 with
                | (rec_env,memos,uu____14851) ->
                    let uu____14904 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____15215 =
                               let uu____15222 =
                                 let uu____15223 =
                                   let uu____15254 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15254, false)
                                    in
                                 Clos uu____15223  in
                               (FStar_Pervasives_Native.None, uu____15222)
                                in
                             uu____15215 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let uu____15367 =
                      let uu____15368 = should_reify cfg stack  in
                      Prims.op_Negation uu____15368  in
                    if uu____15367
                    then
                      let t3 = norm cfg env [] t2  in
                      let stack1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack  in
                      let cfg1 =
                        let uu____15378 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations)
                           in
                        if uu____15378
                        then
                          let uu___133_15379 = cfg  in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___133_15379.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___133_15379.primitive_steps);
                            strong = (uu___133_15379.strong);
                            memoize_lazy = (uu___133_15379.memoize_lazy)
                          }
                        else
                          (let uu___134_15381 = cfg  in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___134_15381.tcenv);
                             delta_level = (uu___134_15381.delta_level);
                             primitive_steps =
                               (uu___134_15381.primitive_steps);
                             strong = (uu___134_15381.strong);
                             memoize_lazy = (uu___134_15381.memoize_lazy)
                           })
                         in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack1) head1
                    else
                      (let uu____15383 =
                         let uu____15384 = FStar_Syntax_Subst.compress head1
                            in
                         uu____15384.FStar_Syntax_Syntax.n  in
                       match uu____15383 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____15402 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____15402 with
                            | (uu____15403,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15409 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15417 =
                                         let uu____15418 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15418.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15417 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15424,uu____15425))
                                           ->
                                           let uu____15434 =
                                             let uu____15435 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15435.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15434 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15441,msrc,uu____15443))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15452 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15452
                                            | uu____15453 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15454 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15455 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15455 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___135_15460 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___135_15460.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___135_15460.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___135_15460.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            }  in
                                          let uu____15461 =
                                            FStar_List.tl stack  in
                                          let uu____15462 =
                                            let uu____15463 =
                                              let uu____15466 =
                                                let uu____15467 =
                                                  let uu____15480 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
                                                    uu____15480)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15467
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15466
                                               in
                                            uu____15463
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env uu____15461
                                            uu____15462
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15496 =
                                            let uu____15497 = is_return body
                                               in
                                            match uu____15497 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15501;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15502;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15507 -> false  in
                                          if uu____15496
                                          then
                                            norm cfg env stack
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let head2 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef
                                                in
                                             let body1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body
                                                in
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
                                               }  in
                                             let body2 =
                                               let uu____15531 =
                                                 let uu____15534 =
                                                   let uu____15535 =
                                                     let uu____15552 =
                                                       let uu____15555 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____15555]  in
                                                     (uu____15552, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc))
                                                      in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____15535
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15534
                                                  in
                                               uu____15531
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos
                                                in
                                             let close1 =
                                               closure_as_term cfg env  in
                                             let bind_inst =
                                               let uu____15571 =
                                                 let uu____15572 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr
                                                    in
                                                 uu____15572.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____15571 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____15578::uu____15579::[])
                                                   ->
                                                   let uu____15586 =
                                                     let uu____15589 =
                                                       let uu____15590 =
                                                         let uu____15597 =
                                                           let uu____15600 =
                                                             let uu____15601
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp
                                                                in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____15601
                                                              in
                                                           let uu____15602 =
                                                             let uu____15605
                                                               =
                                                               let uu____15606
                                                                 = close1 t2
                                                                  in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____15606
                                                                in
                                                             [uu____15605]
                                                              in
                                                           uu____15600 ::
                                                             uu____15602
                                                            in
                                                         (bind1, uu____15597)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____15590
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15589
                                                      in
                                                   uu____15586
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____15614 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects"
                                                in
                                             let reified =
                                               let uu____15620 =
                                                 let uu____15623 =
                                                   let uu____15624 =
                                                     let uu____15639 =
                                                       let uu____15642 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15643 =
                                                         let uu____15646 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2
                                                            in
                                                         let uu____15647 =
                                                           let uu____15650 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let uu____15651 =
                                                             let uu____15654
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2
                                                                in
                                                             let uu____15655
                                                               =
                                                               let uu____15658
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let uu____15659
                                                                 =
                                                                 let uu____15662
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2
                                                                    in
                                                                 [uu____15662]
                                                                  in
                                                               uu____15658 ::
                                                                 uu____15659
                                                                in
                                                             uu____15654 ::
                                                               uu____15655
                                                              in
                                                           uu____15650 ::
                                                             uu____15651
                                                            in
                                                         uu____15646 ::
                                                           uu____15647
                                                          in
                                                       uu____15642 ::
                                                         uu____15643
                                                        in
                                                     (bind_inst, uu____15639)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15624
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15623
                                                  in
                                               uu____15620
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____15670 =
                                               FStar_List.tl stack  in
                                             norm cfg env uu____15670 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____15694 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____15694 with
                            | (uu____15695,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____15730 =
                                        let uu____15731 =
                                          FStar_Syntax_Subst.compress t3  in
                                        uu____15731.FStar_Syntax_Syntax.n  in
                                      match uu____15730 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____15737) -> t4
                                      | uu____15742 -> head2  in
                                    let uu____15743 =
                                      let uu____15744 =
                                        FStar_Syntax_Subst.compress t4  in
                                      uu____15744.FStar_Syntax_Syntax.n  in
                                    match uu____15743 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____15750 ->
                                        FStar_Pervasives_Native.None
                                     in
                                  let uu____15751 = maybe_extract_fv head2
                                     in
                                  match uu____15751 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____15761 =
                                        FStar_Syntax_Syntax.lid_of_fv x  in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____15761
                                      ->
                                      let head3 = norm cfg env [] head2  in
                                      let action_unfolded =
                                        let uu____15766 =
                                          maybe_extract_fv head3  in
                                        match uu____15766 with
                                        | FStar_Pervasives_Native.Some
                                            uu____15771 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____15772 ->
                                            FStar_Pervasives_Native.Some
                                              false
                                         in
                                      (head3, action_unfolded)
                                  | uu____15777 ->
                                      (head2, FStar_Pervasives_Native.None)
                                   in
                                ((let is_arg_impure uu____15792 =
                                    match uu____15792 with
                                    | (e,q) ->
                                        let uu____15799 =
                                          let uu____15800 =
                                            FStar_Syntax_Subst.compress e  in
                                          uu____15800.FStar_Syntax_Syntax.n
                                           in
                                        (match uu____15799 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____15815 -> false)
                                     in
                                  let uu____15816 =
                                    let uu____15817 =
                                      let uu____15824 =
                                        FStar_Syntax_Syntax.as_arg head_app
                                         in
                                      uu____15824 :: args  in
                                    FStar_Util.for_some is_arg_impure
                                      uu____15817
                                     in
                                  if uu____15816
                                  then
                                    let uu____15829 =
                                      let uu____15830 =
                                        FStar_Syntax_Print.term_to_string
                                          head1
                                         in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____15830
                                       in
                                    failwith uu____15829
                                  else ());
                                 (let uu____15832 =
                                    maybe_unfold_action head_app  in
                                  match uu____15832 with
                                  | (head_app1,found_action) ->
                                      let mk1 tm =
                                        FStar_Syntax_Syntax.mk tm
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos
                                         in
                                      let body =
                                        mk1
                                          (FStar_Syntax_Syntax.Tm_app
                                             (head_app1, args))
                                         in
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
                                            ) -> body
                                         in
                                      let uu____15871 = FStar_List.tl stack
                                         in
                                      norm cfg env uu____15871 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____15885 = closure_as_term cfg env t'  in
                             reify_lift cfg.tcenv e msrc mtgt uu____15885  in
                           let uu____15886 = FStar_List.tl stack  in
                           norm cfg env uu____15886 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____16007  ->
                                     match uu____16007 with
                                     | (pat,wopt,tm) ->
                                         let uu____16055 =
                                           FStar_Syntax_Util.mk_reify tm  in
                                         (pat, wopt, uu____16055)))
                              in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____16087 = FStar_List.tl stack  in
                           norm cfg env uu____16087 tm
                       | uu____16088 -> norm cfg env stack head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let uu____16096 = should_reify cfg stack  in
                    if uu____16096
                    then
                      let uu____16097 = FStar_List.tl stack  in
                      let uu____16098 =
                        let uu____16099 = closure_as_term cfg env t2  in
                        reify_lift cfg.tcenv head1 m1 m' uu____16099  in
                      norm cfg env uu____16097 uu____16098
                    else
                      (let t3 = norm cfg env [] t2  in
                       let uu____16102 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations))
                          in
                       if uu____16102
                       then
                         let stack1 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack  in
                         let cfg1 =
                           let uu___136_16111 = cfg  in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___136_16111.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___136_16111.primitive_steps);
                             strong = (uu___136_16111.strong);
                             memoize_lazy = (uu___136_16111.memoize_lazy)
                           }  in
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
                | uu____16113 ->
                    if FStar_List.contains Unmeta cfg.steps
                    then norm cfg env stack head1
                    else
                      (match stack with
                       | uu____16115::uu____16116 ->
                           (match m with
                            | FStar_Syntax_Syntax.Meta_labeled
                                (l,r,uu____16121) ->
                                norm cfg env ((Meta (m, r)) :: stack) head1
                            | FStar_Syntax_Syntax.Meta_alien uu____16122 ->
                                rebuild cfg env stack t1
                            | FStar_Syntax_Syntax.Meta_pattern args ->
                                let args1 = norm_pattern_args cfg env args
                                   in
                                norm cfg env
                                  ((Meta
                                      ((FStar_Syntax_Syntax.Meta_pattern
                                          args1),
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack) head1
                            | uu____16153 -> norm cfg env stack head1)
                       | [] ->
                           let head2 = norm cfg env [] head1  in
                           let m1 =
                             match m with
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let uu____16167 =
                                   norm_pattern_args cfg env args  in
                                 FStar_Syntax_Syntax.Meta_pattern uu____16167
                             | uu____16178 -> m  in
                           let t2 =
                             mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                               t1.FStar_Syntax_Syntax.pos
                              in
                           rebuild cfg env stack t2)))

and (do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____16190 = FStar_Syntax_Syntax.range_of_fv f  in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16190  in
            let uu____16191 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            match uu____16191 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16204  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16215  ->
                      let uu____16216 = FStar_Syntax_Print.term_to_string t0
                         in
                      let uu____16217 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16216
                        uu____16217);
                 (let t1 =
                    let uu____16219 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains
                           (UnfoldUntil FStar_Syntax_Syntax.Delta_constant))
                       in
                    if uu____16219
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t
                     in
                  let n1 = FStar_List.length us  in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack with
                    | (UnivArgs (us',uu____16229))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env)
                           in
                        norm cfg env1 stack1 t1
                    | uu____16284 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____16287 ->
                        let uu____16290 =
                          let uu____16291 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16291
                           in
                        failwith uu____16290
                  else norm cfg env stack t1))

and (reify_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
              let uu____16301 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____16301 with
              | (uu____16302,return_repr) ->
                  let return_inst =
                    let uu____16311 =
                      let uu____16312 =
                        FStar_Syntax_Subst.compress return_repr  in
                      uu____16312.FStar_Syntax_Syntax.n  in
                    match uu____16311 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____16318::[]) ->
                        let uu____16325 =
                          let uu____16328 =
                            let uu____16329 =
                              let uu____16336 =
                                let uu____16339 =
                                  env.FStar_TypeChecker_Env.universe_of env t
                                   in
                                [uu____16339]  in
                              (return_tm, uu____16336)  in
                            FStar_Syntax_Syntax.Tm_uinst uu____16329  in
                          FStar_Syntax_Syntax.mk uu____16328  in
                        uu____16325 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____16347 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  let uu____16350 =
                    let uu____16353 =
                      let uu____16354 =
                        let uu____16369 =
                          let uu____16372 = FStar_Syntax_Syntax.as_arg t  in
                          let uu____16373 =
                            let uu____16376 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____16376]  in
                          uu____16372 :: uu____16373  in
                        (return_inst, uu____16369)  in
                      FStar_Syntax_Syntax.Tm_app uu____16354  in
                    FStar_Syntax_Syntax.mk uu____16353  in
                  uu____16350 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____16385 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____16385 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16388 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____16388
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16389;
                     FStar_TypeChecker_Env.mtarget = uu____16390;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16391;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16406;
                     FStar_TypeChecker_Env.mtarget = uu____16407;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16408;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16432 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____16433 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____16432 t FStar_Syntax_Syntax.tun uu____16433)

and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____16489  ->
                   match uu____16489 with
                   | (a,imp) ->
                       let uu____16500 = norm cfg env [] a  in
                       (uu____16500, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___137_16514 = comp  in
            let uu____16515 =
              let uu____16516 =
                let uu____16525 = norm cfg env [] t  in
                let uu____16526 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____16525, uu____16526)  in
              FStar_Syntax_Syntax.Total uu____16516  in
            {
              FStar_Syntax_Syntax.n = uu____16515;
              FStar_Syntax_Syntax.pos =
                (uu___137_16514.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16514.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___138_16541 = comp  in
            let uu____16542 =
              let uu____16543 =
                let uu____16552 = norm cfg env [] t  in
                let uu____16553 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____16552, uu____16553)  in
              FStar_Syntax_Syntax.GTotal uu____16543  in
            {
              FStar_Syntax_Syntax.n = uu____16542;
              FStar_Syntax_Syntax.pos =
                (uu___138_16541.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___138_16541.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16605  ->
                      match uu____16605 with
                      | (a,i) ->
                          let uu____16616 = norm cfg env [] a  in
                          (uu____16616, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___84_16627  ->
                      match uu___84_16627 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16631 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____16631
                      | f -> f))
               in
            let uu___139_16635 = comp  in
            let uu____16636 =
              let uu____16637 =
                let uu___140_16638 = ct  in
                let uu____16639 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____16640 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____16643 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16639;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___140_16638.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16640;
                  FStar_Syntax_Syntax.effect_args = uu____16643;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____16637  in
            {
              FStar_Syntax_Syntax.n = uu____16636;
              FStar_Syntax_Syntax.pos =
                (uu___139_16635.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_16635.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____16654  ->
        match uu____16654 with
        | (x,imp) ->
            let uu____16657 =
              let uu___141_16658 = x  in
              let uu____16659 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___141_16658.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___141_16658.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16659
              }  in
            (uu____16657, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16665 =
          FStar_List.fold_left
            (fun uu____16683  ->
               fun b  ->
                 match uu____16683 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16665 with | (nbs,uu____16723) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____16739 =
              let uu___142_16740 = rc  in
              let uu____16741 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___142_16740.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16741;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___142_16740.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16739
        | uu____16748 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16761  ->
               let uu____16762 = FStar_Syntax_Print.tag_of_term t  in
               let uu____16763 = FStar_Syntax_Print.term_to_string t  in
               let uu____16764 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____16771 =
                 let uu____16772 =
                   let uu____16775 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16775
                    in
                 stack_to_string uu____16772  in
               FStar_Util.print4
                 ">>> %s\\Rebuild %s with %s env elements and top of the stack %s \n"
                 uu____16762 uu____16763 uu____16764 uu____16771);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16804 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms")
                    in
                 if uu____16804
                 then
                   let time_now = FStar_Util.now ()  in
                   let uu____16806 =
                     let uu____16807 =
                       let uu____16808 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____16808  in
                     FStar_Util.string_of_int uu____16807  in
                   let uu____16813 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____16814 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16806 uu____16813 uu____16814
                 else ());
                rebuild cfg env stack1 t)
           | (Steps (s,ps,dl))::stack1 ->
               rebuild
                 (let uu___143_16832 = cfg  in
                  {
                    steps = s;
                    tcenv = (uu___143_16832.tcenv);
                    delta_level = dl;
                    primitive_steps = ps;
                    strong = (uu___143_16832.strong);
                    memoize_lazy = (uu___143_16832.memoize_lazy)
                  }) env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16881  ->
                     let uu____16882 = FStar_Syntax_Print.term_to_string t
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16882);
                rebuild cfg env stack1 t)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t  in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env' stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs  in
               let lopt1 = norm_lcomp_opt cfg env'' lopt  in
               let uu____16918 =
                 let uu___144_16919 = FStar_Syntax_Util.abs bs1 t lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___144_16919.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___144_16919.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____16918
           | (Arg (Univ uu____16920,uu____16921,uu____16922))::uu____16923 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16926,uu____16927))::uu____16928 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16944),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16997  ->
                     let uu____16998 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16998);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm  in
                     let t1 =
                       FStar_Syntax_Syntax.extend_app t (arg, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t1
                   else
                     (let stack2 = (App (env, t, aq, r)) :: stack1  in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____17008 = FStar_ST.op_Bang m  in
                   match uu____17008 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm  in
                         let t1 =
                           FStar_Syntax_Syntax.extend_app t (arg, aq)
                             FStar_Pervasives_Native.None r
                            in
                         rebuild cfg env_arg stack1 t1
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____17145,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               let uu____17188 = maybe_simplify cfg env1 stack1 t1  in
               rebuild cfg env1 stack1 uu____17188
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17200  ->
                     let uu____17201 = FStar_Syntax_Print.term_to_string t
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17201);
                (let scrutinee = t  in
                 let norm_and_rebuild_match uu____17206 =
                   log cfg
                     (fun uu____17211  ->
                        let uu____17212 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____17213 =
                          let uu____17214 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17231  ->
                                    match uu____17231 with
                                    | (p,uu____17241,uu____17242) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____17214
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17212 uu____17213);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps)
                       in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___85_17259  ->
                                match uu___85_17259 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17260 -> false))
                         in
                      let steps' = [Exclude Zeta]  in
                      let uu___145_17264 = cfg  in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___145_17264.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___145_17264.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___145_17264.memoize_lazy)
                      }  in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17296 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17317 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17377  ->
                                    fun uu____17378  ->
                                      match (uu____17377, uu____17378) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17469 = norm_pat env3 p1
                                             in
                                          (match uu____17469 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____17317 with
                           | (pats1,env3) ->
                               ((let uu___146_17551 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___146_17551.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___147_17570 = x  in
                            let uu____17571 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_17570.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_17570.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17571
                            }  in
                          ((let uu___148_17585 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___148_17585.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___149_17596 = x  in
                            let uu____17597 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___149_17596.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___149_17596.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17597
                            }  in
                          ((let uu___150_17611 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___150_17611.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___151_17627 = x  in
                            let uu____17628 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___151_17627.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___151_17627.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17628
                            }  in
                          let t2 = norm_or_whnf env2 t1  in
                          ((let uu___152_17635 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___152_17635.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17645 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17659 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____17659 with
                                  | (p,wopt,e) ->
                                      let uu____17679 = norm_pat env1 p  in
                                      (match uu____17679 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17704 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17704
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____17710 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____17710)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17720) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17725 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17726;
                         FStar_Syntax_Syntax.fv_delta = uu____17727;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17728;
                         FStar_Syntax_Syntax.fv_delta = uu____17729;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17730);_}
                       -> true
                   | uu____17737 -> false  in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b  in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r
                          in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch
                    in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                      in
                   let uu____17882 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____17882 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17969 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____18008 ->
                                 let uu____18009 =
                                   let uu____18010 = is_cons head1  in
                                   Prims.op_Negation uu____18010  in
                                 FStar_Util.Inr uu____18009)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____18035 =
                              let uu____18036 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____18036.FStar_Syntax_Syntax.n  in
                            (match uu____18035 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____18054 ->
                                 let uu____18055 =
                                   let uu____18056 = is_cons head1  in
                                   Prims.op_Negation uu____18056  in
                                 FStar_Util.Inr uu____18055))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____18125)::rest_a,(p1,uu____18128)::rest_p) ->
                       let uu____18172 = matches_pat t1 p1  in
                       (match uu____18172 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18221 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18327 = matches_pat scrutinee1 p1  in
                       (match uu____18327 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18367  ->
                                  let uu____18368 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____18369 =
                                    let uu____18370 =
                                      FStar_List.map
                                        (fun uu____18380  ->
                                           match uu____18380 with
                                           | (uu____18385,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s
                                       in
                                    FStar_All.pipe_right uu____18370
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18368 uu____18369);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18416  ->
                                       match uu____18416 with
                                       | (bv,t1) ->
                                           let uu____18439 =
                                             let uu____18446 =
                                               let uu____18449 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____18449
                                                in
                                             let uu____18450 =
                                               let uu____18451 =
                                                 let uu____18482 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1))
                                                    in
                                                 ([], t1, uu____18482, false)
                                                  in
                                               Clos uu____18451  in
                                             (uu____18446, uu____18450)  in
                                           uu____18439 :: env2) env1 s
                                 in
                              let uu____18599 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____18599)))
                    in
                 let uu____18600 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota))
                    in
                 if uu____18600
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___86_18621  ->
                match uu___86_18621 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18625 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18631 -> d  in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true
      }
  
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e  in
          let c1 =
            let uu___153_18656 = config s e  in
            {
              steps = (uu___153_18656.steps);
              tcenv = (uu___153_18656.tcenv);
              delta_level = (uu___153_18656.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___153_18656.strong);
              memoize_lazy = (uu___153_18656.memoize_lazy)
            }  in
          norm c1 [] [] t
  
let (normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____18681 = config s e  in norm_comp uu____18681 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____18694 = config [] env  in norm_universe uu____18694 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____18712 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____18712  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18719 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___154_18738 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___154_18738.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___154_18738.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____18745 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____18745
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
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___155_18754 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___155_18754.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___155_18754.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___155_18754.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___156_18756 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___156_18756.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___156_18756.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___156_18756.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___156_18756.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___157_18757 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___157_18757.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___157_18757.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18759 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____18771 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____18771  in
      let uu____18778 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____18778
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18782  ->
                 let uu____18783 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____18783)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____18800 =
                let uu____18805 =
                  let uu____18806 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18806
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____18805)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18800);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18817 = config [AllowUnboundUniverses] env  in
          norm_comp uu____18817 [] c
        with
        | e ->
            ((let uu____18830 =
                let uu____18835 =
                  let uu____18836 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18836
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____18835)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18830);
             c)
         in
      FStar_Syntax_Print.comp_to_string c1
  
let (normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0  in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____18873 =
                     let uu____18874 =
                       let uu____18881 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____18881)  in
                     FStar_Syntax_Syntax.Tm_refine uu____18874  in
                   mk uu____18873 t01.FStar_Syntax_Syntax.pos
               | uu____18886 -> t2)
          | uu____18887 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
  
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
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
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____18927 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____18927 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18956 ->
                 let uu____18963 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____18963 with
                  | (actuals,uu____18973,uu____18974) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18988 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____18988 with
                         | (binders,args) ->
                             let uu____19005 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____19005
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____19013 ->
          let uu____19014 = FStar_Syntax_Util.head_and_args t  in
          (match uu____19014 with
           | (head1,args) ->
               let uu____19051 =
                 let uu____19052 = FStar_Syntax_Subst.compress head1  in
                 uu____19052.FStar_Syntax_Syntax.n  in
               (match uu____19051 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____19055,thead) ->
                    let uu____19081 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____19081 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____19123 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___162_19131 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___162_19131.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___162_19131.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___162_19131.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___162_19131.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___162_19131.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___162_19131.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___162_19131.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___162_19131.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___162_19131.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___162_19131.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___162_19131.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___162_19131.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___162_19131.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___162_19131.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___162_19131.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___162_19131.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___162_19131.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___162_19131.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___162_19131.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___162_19131.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___162_19131.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___162_19131.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___162_19131.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___162_19131.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___162_19131.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___162_19131.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___162_19131.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___162_19131.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___162_19131.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___162_19131.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___162_19131.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___162_19131.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____19123 with
                            | (uu____19132,ty,uu____19134) ->
                                eta_expand_with_type env t ty))
                | uu____19135 ->
                    let uu____19136 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___163_19144 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___163_19144.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___163_19144.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___163_19144.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___163_19144.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___163_19144.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___163_19144.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___163_19144.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___163_19144.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___163_19144.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___163_19144.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___163_19144.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___163_19144.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___163_19144.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___163_19144.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___163_19144.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___163_19144.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___163_19144.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___163_19144.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___163_19144.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___163_19144.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___163_19144.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___163_19144.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___163_19144.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___163_19144.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___163_19144.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___163_19144.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___163_19144.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___163_19144.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___163_19144.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___163_19144.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___163_19144.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___163_19144.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____19136 with
                     | (uu____19145,ty,uu____19147) ->
                         eta_expand_with_type env t ty)))
  
let (elim_uvars_aux_tc :
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
            FStar_Pervasives_Native.tuple3)
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
            | (uu____19221,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19227,FStar_Util.Inl t) ->
                let uu____19233 =
                  let uu____19236 =
                    let uu____19237 =
                      let uu____19250 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____19250)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____19237  in
                  FStar_Syntax_Syntax.mk uu____19236  in
                uu____19233 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____19254 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____19254 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let uu____19281 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19336 ->
                    let uu____19337 =
                      let uu____19346 =
                        let uu____19347 = FStar_Syntax_Subst.compress t3  in
                        uu____19347.FStar_Syntax_Syntax.n  in
                      (uu____19346, tc)  in
                    (match uu____19337 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19372) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19409) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19448,FStar_Util.Inl uu____19449) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19472 -> failwith "Impossible")
                 in
              (match uu____19281 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____19577 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____19577 with
          | (univ_names1,binders1,tc) ->
              let uu____19635 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____19635)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____19670 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____19670 with
          | (univ_names1,binders1,tc) ->
              let uu____19730 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____19730)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19763 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____19763 with
           | (univ_names1,binders1,typ1) ->
               let uu___164_19791 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19791.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19791.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19791.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19791.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___165_19812 = s  in
          let uu____19813 =
            let uu____19814 =
              let uu____19823 = FStar_List.map (elim_uvars env) sigs  in
              (uu____19823, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____19814  in
          {
            FStar_Syntax_Syntax.sigel = uu____19813;
            FStar_Syntax_Syntax.sigrng =
              (uu___165_19812.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___165_19812.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___165_19812.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___165_19812.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19840 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____19840 with
           | (univ_names1,uu____19858,typ1) ->
               let uu___166_19872 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___166_19872.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___166_19872.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___166_19872.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___166_19872.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19878 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____19878 with
           | (univ_names1,uu____19896,typ1) ->
               let uu___167_19910 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___167_19910.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___167_19910.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___167_19910.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___167_19910.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19944 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____19944 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19967 =
                            let uu____19968 =
                              FStar_Syntax_Subst.subst opening t  in
                            remove_uvar_solutions env uu____19968  in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19967
                           in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___168_19971 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___168_19971.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___168_19971.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        }))
             in
          let uu___169_19972 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___169_19972.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___169_19972.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___169_19972.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___169_19972.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___170_19984 = s  in
          let uu____19985 =
            let uu____19986 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____19986  in
          {
            FStar_Syntax_Syntax.sigel = uu____19985;
            FStar_Syntax_Syntax.sigrng =
              (uu___170_19984.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___170_19984.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___170_19984.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___170_19984.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19990 = elim_uvars_aux_t env us [] t  in
          (match uu____19990 with
           | (us1,uu____20008,t1) ->
               let uu___171_20022 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___171_20022.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___171_20022.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___171_20022.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___171_20022.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20023 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20025 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____20025 with
           | (univs1,binders,signature) ->
               let uu____20053 =
                 let uu____20062 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____20062 with
                 | (univs_opening,univs2) ->
                     let uu____20089 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____20089)
                  in
               (match uu____20053 with
                | (univs_opening,univs_closing) ->
                    let uu____20106 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____20112 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____20113 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____20112, uu____20113)  in
                    (match uu____20106 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____20135 =
                           match uu____20135 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____20153 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____20153 with
                                | (us1,t1) ->
                                    let uu____20164 =
                                      let uu____20169 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____20176 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____20169, uu____20176)  in
                                    (match uu____20164 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20189 =
                                           let uu____20194 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____20203 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____20194, uu____20203)  in
                                         (match uu____20189 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20219 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20219
                                                 in
                                              let uu____20220 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____20220 with
                                               | (uu____20241,uu____20242,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20257 =
                                                       let uu____20258 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20258
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20257
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____20263 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____20263 with
                           | (uu____20276,uu____20277,t1) -> t1  in
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
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____20337 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____20354 =
                               let uu____20355 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____20355.FStar_Syntax_Syntax.n  in
                             match uu____20354 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20414 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____20443 =
                               let uu____20444 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____20444.FStar_Syntax_Syntax.n  in
                             match uu____20443 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20465) ->
                                 let uu____20486 = destruct_action_body body
                                    in
                                 (match uu____20486 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20531 ->
                                 let uu____20532 = destruct_action_body t  in
                                 (match uu____20532 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____20581 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____20581 with
                           | (action_univs,t) ->
                               let uu____20590 = destruct_action_typ_templ t
                                  in
                               (match uu____20590 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___172_20631 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___172_20631.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___172_20631.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___173_20633 = ed  in
                           let uu____20634 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____20635 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____20636 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____20637 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____20638 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____20639 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____20640 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____20641 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____20642 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____20643 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____20644 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____20645 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____20646 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____20647 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___173_20633.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___173_20633.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20634;
                             FStar_Syntax_Syntax.bind_wp = uu____20635;
                             FStar_Syntax_Syntax.if_then_else = uu____20636;
                             FStar_Syntax_Syntax.ite_wp = uu____20637;
                             FStar_Syntax_Syntax.stronger = uu____20638;
                             FStar_Syntax_Syntax.close_wp = uu____20639;
                             FStar_Syntax_Syntax.assert_p = uu____20640;
                             FStar_Syntax_Syntax.assume_p = uu____20641;
                             FStar_Syntax_Syntax.null_wp = uu____20642;
                             FStar_Syntax_Syntax.trivial = uu____20643;
                             FStar_Syntax_Syntax.repr = uu____20644;
                             FStar_Syntax_Syntax.return_repr = uu____20645;
                             FStar_Syntax_Syntax.bind_repr = uu____20646;
                             FStar_Syntax_Syntax.actions = uu____20647
                           }  in
                         let uu___174_20650 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___174_20650.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___174_20650.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___174_20650.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___174_20650.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___87_20667 =
            match uu___87_20667 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20694 = elim_uvars_aux_t env us [] t  in
                (match uu____20694 with
                 | (us1,uu____20718,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___175_20737 = sub_eff  in
            let uu____20738 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____20741 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___175_20737.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___175_20737.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20738;
              FStar_Syntax_Syntax.lift = uu____20741
            }  in
          let uu___176_20744 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___176_20744.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___176_20744.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___176_20744.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___176_20744.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20754 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____20754 with
           | (univ_names1,binders1,comp1) ->
               let uu___177_20788 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___177_20788.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___177_20788.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___177_20788.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___177_20788.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20799 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  