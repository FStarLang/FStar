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
  fun uu___72_501  ->
    match uu___72_501 with
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
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool }[@@deriving show]
let (__proj__Mkcfg__item__steps : cfg -> steps) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
  
let (__proj__Mkcfg__item__primitive_steps : cfg -> primitive_step Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
  
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____830 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____866 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____902 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____971 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1013 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1069 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1109 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1141 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1177 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1193 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____1218 .
    'Auu____1218 ->
      FStar_Range.range -> 'Auu____1218 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1272 = FStar_ST.op_Bang r  in
          match uu____1272 with
          | FStar_Pervasives_Native.Some uu____1320 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____1374 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____1374 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___73_1381  ->
    match uu___73_1381 with
    | Arg (c,uu____1383,uu____1384) ->
        let uu____1385 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1385
    | MemoLazy uu____1386 -> "MemoLazy"
    | Abs (uu____1393,bs,uu____1395,uu____1396,uu____1397) ->
        let uu____1402 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1402
    | UnivArgs uu____1407 -> "UnivArgs"
    | Match uu____1414 -> "Match"
    | App (uu____1421,t,uu____1423,uu____1424) ->
        let uu____1425 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1425
    | Meta (m,uu____1427) -> "Meta"
    | Let uu____1428 -> "Let"
    | Cfg uu____1437 -> "Cfg"
    | Debug (t,uu____1439) ->
        let uu____1440 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1440
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1448 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1448 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1464 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____1464 then f () else ()
  
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1477 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops"))
         in
      if uu____1477 then f () else ()
  
let is_empty : 'Auu____1481 . 'Auu____1481 Prims.list -> Prims.bool =
  fun uu___74_1487  ->
    match uu___74_1487 with | [] -> true | uu____1490 -> false
  
let lookup_bvar :
  'Auu____1497 'Auu____1498 .
    ('Auu____1498,'Auu____1497) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1497
  =
  fun env  ->
    fun x  ->
      try
        let uu____1522 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____1522
      with
      | uu____1535 ->
          let uu____1536 =
            let uu____1537 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____1537  in
          failwith uu____1536
  
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
          let uu____1574 =
            FStar_List.fold_left
              (fun uu____1600  ->
                 fun u1  ->
                   match uu____1600 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1625 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1625 with
                        | (k_u,n1) ->
                            let uu____1640 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1640
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1574 with
          | (uu____1658,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1683 =
                   let uu____1684 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____1684  in
                 match uu____1683 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1702 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1711 ->
                   let uu____1712 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____1712
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1718 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1727 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1736 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1743 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1743 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1760 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1760 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1768 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1776 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1776 with
                                  | (uu____1781,m) -> n1 <= m))
                           in
                        if uu____1768 then rest1 else us1
                    | uu____1786 -> us1)
               | uu____1791 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1795 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1795
           in
        let uu____1798 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____1798
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1800 = aux u  in
           match uu____1800 with
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
          (fun uu____1904  ->
             let uu____1905 = FStar_Syntax_Print.tag_of_term t  in
             let uu____1906 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1905
               uu____1906);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1913 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1915 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1940 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1941 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1942 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1943 ->
                  let uu____1960 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars)
                     in
                  if uu____1960
                  then
                    let uu____1961 =
                      let uu____1962 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____1963 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1962 uu____1963
                       in
                    failwith uu____1961
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1966 =
                    let uu____1967 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____1967  in
                  mk uu____1966 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1974 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1974
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1976 = lookup_bvar env x  in
                  (match uu____1976 with
                   | Univ uu____1979 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1982,uu____1983) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2095 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2095 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____2123 =
                         let uu____2124 =
                           let uu____2141 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____2141)  in
                         FStar_Syntax_Syntax.Tm_abs uu____2124  in
                       mk uu____2123 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2172 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2172 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2214 =
                    let uu____2225 =
                      let uu____2232 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____2232]  in
                    closures_as_binders_delayed cfg env uu____2225  in
                  (match uu____2214 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____2250 =
                         let uu____2251 =
                           let uu____2258 =
                             let uu____2259 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____2259
                               FStar_Pervasives_Native.fst
                              in
                           (uu____2258, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____2251  in
                       mk uu____2250 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2350 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____2350
                    | FStar_Util.Inr c ->
                        let uu____2364 = close_comp cfg env c  in
                        FStar_Util.Inr uu____2364
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____2380 =
                    let uu____2381 =
                      let uu____2408 = closure_as_term_delayed cfg env t11
                         in
                      (uu____2408, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2381  in
                  mk uu____2380 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2459 =
                    let uu____2460 =
                      let uu____2467 = closure_as_term_delayed cfg env t'  in
                      let uu____2470 =
                        let uu____2471 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____2471  in
                      (uu____2467, uu____2470)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2460  in
                  mk uu____2459 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2531 =
                    let uu____2532 =
                      let uu____2539 = closure_as_term_delayed cfg env t'  in
                      let uu____2542 =
                        let uu____2543 =
                          let uu____2550 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____2550)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____2543  in
                      (uu____2539, uu____2542)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2532  in
                  mk uu____2531 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2569 =
                    let uu____2570 =
                      let uu____2577 = closure_as_term_delayed cfg env t'  in
                      let uu____2580 =
                        let uu____2581 =
                          let uu____2590 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____2590)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2581  in
                      (uu____2577, uu____2580)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2570  in
                  mk uu____2569 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2603 =
                    let uu____2604 =
                      let uu____2611 = closure_as_term_delayed cfg env t'  in
                      (uu____2611, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2604  in
                  mk uu____2603 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2651  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____2670 =
                    let uu____2681 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____2681
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____2700 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___93_2712 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_2712.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_2712.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2700))
                     in
                  (match uu____2670 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___94_2728 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_2728.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_2728.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2739,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2798  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____2823 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____2823
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2843  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____2865 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____2865
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___95_2877 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___95_2877.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___95_2877.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___96_2878 = lb  in
                    let uu____2879 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___96_2878.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___96_2878.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2879
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2909  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____2998 =
                    match uu____2998 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3053 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3074 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3134  ->
                                        fun uu____3135  ->
                                          match (uu____3134, uu____3135) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3226 =
                                                norm_pat env3 p1  in
                                              (match uu____3226 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____3074 with
                               | (pats1,env3) ->
                                   ((let uu___97_3308 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___97_3308.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___98_3327 = x  in
                                let uu____3328 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___98_3327.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_3327.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3328
                                }  in
                              ((let uu___99_3342 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___99_3342.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___100_3353 = x  in
                                let uu____3354 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___100_3353.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___100_3353.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3354
                                }  in
                              ((let uu___101_3368 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___101_3368.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___102_3384 = x  in
                                let uu____3385 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3384.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3384.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3385
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___103_3392 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3392.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____3395 = norm_pat env1 pat  in
                        (match uu____3395 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3424 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____3424
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____3430 =
                    let uu____3431 =
                      let uu____3454 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____3454)  in
                    FStar_Syntax_Syntax.Tm_match uu____3431  in
                  mk uu____3430 t1.FStar_Syntax_Syntax.pos))

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
        | uu____3540 -> closure_as_term cfg env t

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
        | uu____3566 ->
            FStar_List.map
              (fun uu____3583  ->
                 match uu____3583 with
                 | (x,imp) ->
                     let uu____3602 = closure_as_term_delayed cfg env x  in
                     (uu____3602, imp)) args

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
        let uu____3616 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3665  ->
                  fun uu____3666  ->
                    match (uu____3665, uu____3666) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___104_3736 = b  in
                          let uu____3737 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___104_3736.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___104_3736.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3737
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____3616 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____3830 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3843 = closure_as_term_delayed cfg env t  in
                 let uu____3844 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____3843 uu____3844
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3857 = closure_as_term_delayed cfg env t  in
                 let uu____3858 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3857 uu____3858
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
                        (fun uu___75_3884  ->
                           match uu___75_3884 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3888 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____3888
                           | f -> f))
                    in
                 let uu____3892 =
                   let uu___105_3893 = c1  in
                   let uu____3894 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3894;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___105_3893.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____3892)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___76_3904  ->
            match uu___76_3904 with
            | FStar_Syntax_Syntax.DECREASES uu____3905 -> false
            | uu____3908 -> true))

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
                   (fun uu___77_3926  ->
                      match uu___77_3926 with
                      | FStar_Syntax_Syntax.DECREASES uu____3927 -> false
                      | uu____3930 -> true))
               in
            let rc1 =
              let uu___106_3932 = rc  in
              let uu____3933 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___106_3932.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3933;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____3940 -> lopt

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
    let uu____4030 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4030  in
  let arg_as_bounded_int uu____4058 =
    match uu____4058 with
    | (a,uu____4070) ->
        let uu____4077 =
          let uu____4078 = FStar_Syntax_Subst.compress a  in
          uu____4078.FStar_Syntax_Syntax.n  in
        (match uu____4077 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4088;
                FStar_Syntax_Syntax.vars = uu____4089;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4091;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4092;_},uu____4093)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4132 =
               let uu____4137 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____4137)  in
             FStar_Pervasives_Native.Some uu____4132
         | uu____4142 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4184 = f a  in FStar_Pervasives_Native.Some uu____4184
    | uu____4185 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4235 = f a0 a1  in FStar_Pervasives_Native.Some uu____4235
    | uu____4236 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____4285 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____4285  in
  let binary_op as_a f res args =
    let uu____4341 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____4341  in
  let as_primitive_step uu____4365 =
    match uu____4365 with
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
           let uu____4413 = f x  in
           FStar_Syntax_Embeddings.embed_int r uu____4413)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4441 = f x y  in
             FStar_Syntax_Embeddings.embed_int r uu____4441)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____4462 = f x  in
           FStar_Syntax_Embeddings.embed_bool r uu____4462)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4490 = f x y  in
             FStar_Syntax_Embeddings.embed_bool r uu____4490)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____4518 = f x y  in
             FStar_Syntax_Embeddings.embed_string r uu____4518)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4635 =
          let uu____4644 = as_a a  in
          let uu____4647 = as_b b  in (uu____4644, uu____4647)  in
        (match uu____4635 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4662 =
               let uu____4663 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____4663  in
             FStar_Pervasives_Native.Some uu____4662
         | uu____4664 -> FStar_Pervasives_Native.None)
    | uu____4673 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____4687 =
        let uu____4688 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____4688  in
      mk uu____4687 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____4698 =
      let uu____4701 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____4701  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4698  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____4733 =
      let uu____4734 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____4734  in
    FStar_Syntax_Embeddings.embed_int rng uu____4733  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4752 = arg_as_string a1  in
        (match uu____4752 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4758 =
               arg_as_list FStar_Syntax_Embeddings.unembed_string_safe a2  in
             (match uu____4758 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4771 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____4771
              | uu____4772 -> FStar_Pervasives_Native.None)
         | uu____4777 -> FStar_Pervasives_Native.None)
    | uu____4780 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____4790 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____4790  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____4814 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4825 =
          let uu____4846 = arg_as_string fn  in
          let uu____4849 = arg_as_int from_line  in
          let uu____4852 = arg_as_int from_col  in
          let uu____4855 = arg_as_int to_line  in
          let uu____4858 = arg_as_int to_col  in
          (uu____4846, uu____4849, uu____4852, uu____4855, uu____4858)  in
        (match uu____4825 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4889 =
                 let uu____4890 = FStar_BigInt.to_int_fs from_l  in
                 let uu____4891 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____4890 uu____4891  in
               let uu____4892 =
                 let uu____4893 = FStar_BigInt.to_int_fs to_l  in
                 let uu____4894 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____4893 uu____4894  in
               FStar_Range.mk_range fn1 uu____4889 uu____4892  in
             let uu____4895 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____4895
         | uu____4900 -> FStar_Pervasives_Native.None)
    | uu____4921 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____4948)::(a1,uu____4950)::(a2,uu____4952)::[] ->
        let uu____4989 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____4989 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5002 -> FStar_Pervasives_Native.None)
    | uu____5003 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____5030)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5039 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____5063 =
      let uu____5078 =
        let uu____5093 =
          let uu____5108 =
            let uu____5123 =
              let uu____5138 =
                let uu____5153 =
                  let uu____5168 =
                    let uu____5183 =
                      let uu____5198 =
                        let uu____5213 =
                          let uu____5228 =
                            let uu____5243 =
                              let uu____5258 =
                                let uu____5273 =
                                  let uu____5288 =
                                    let uu____5303 =
                                      let uu____5318 =
                                        let uu____5333 =
                                          let uu____5348 =
                                            let uu____5363 =
                                              let uu____5378 =
                                                let uu____5391 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____5391,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____5398 =
                                                let uu____5413 =
                                                  let uu____5426 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____5426,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.unembed_char_safe)
                                                       string_of_list'))
                                                   in
                                                let uu____5437 =
                                                  let uu____5452 =
                                                    let uu____5467 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____5467,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____5476 =
                                                    let uu____5493 =
                                                      let uu____5508 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____5508,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____5517 =
                                                      let uu____5534 =
                                                        let uu____5553 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____5553,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____5534]  in
                                                    uu____5493 :: uu____5517
                                                     in
                                                  uu____5452 :: uu____5476
                                                   in
                                                uu____5413 :: uu____5437  in
                                              uu____5378 :: uu____5398  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5363
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5348
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____5333
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____5318
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____5303
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       FStar_Syntax_Embeddings.embed_string
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____5771 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____5771 y)))
                                    :: uu____5288
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5273
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5258
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5243
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5228
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5213
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5198
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
                      :: uu____5183
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5964 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed_bool r uu____5964)))
                    :: uu____5168
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5990 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed_bool r uu____5990)))
                  :: uu____5153
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____6016 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed_bool r uu____6016)))
                :: uu____5138
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5123
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5108
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5093
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5078
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5063
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
               (let uu___107_6561 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6561.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6561.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6565 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6565.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6565.FStar_Syntax_Syntax.vars)
                })
         | uu____6566 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6568)::uu____6569::(a1,uu____6571)::(a2,uu____6573)::[] ->
        let uu____6622 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6622 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6628 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6628.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6628.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6632 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6632.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6632.FStar_Syntax_Syntax.vars)
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
                                      let uu___111_6848 = bv  in
                                      let uu____6849 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_6848.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_6848.FStar_Syntax_Syntax.index);
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
                                      (fun uu___78_6869  ->
                                         match uu___78_6869 with
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
                        | (t,uu____7079)::(r,uu____7081)::[] ->
                            let uu____7108 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____7108 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7112 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7112.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7112.FStar_Syntax_Syntax.vars)
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
        (let uu___113_7168 = cfg  in
         {
           steps = [Primops];
           tcenv = (uu___113_7168.tcenv);
           delta_level = (uu___113_7168.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7168.strong);
           memoize_lazy = (uu___113_7168.memoize_lazy);
           normalize_pure_lets = (uu___113_7168.normalize_pure_lets)
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
               let uu___114_7230 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7230.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7230.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7246;
                      FStar_Syntax_Syntax.vars = uu____7247;_},uu____7248)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7255;
                      FStar_Syntax_Syntax.vars = uu____7256;_},uu____7257)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7263 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____7268 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____7268
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7289 =
                 match uu____7289 with
                 | (t1,q) ->
                     let uu____7302 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____7302 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7330 -> (t1, q))
                  in
               let uu____7339 = FStar_Syntax_Util.head_and_args t  in
               match uu____7339 with
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
                         FStar_Syntax_Syntax.pos = uu____7436;
                         FStar_Syntax_Syntax.vars = uu____7437;_},uu____7438);
                    FStar_Syntax_Syntax.pos = uu____7439;
                    FStar_Syntax_Syntax.vars = uu____7440;_},args)
                 ->
                 let uu____7466 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____7466
                 then
                   let uu____7467 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____7467 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7522)::
                        (uu____7523,(arg,uu____7525))::[] ->
                        maybe_auto_squash arg
                    | (uu____7590,(arg,uu____7592))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7593)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7658)::uu____7659::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7722::(FStar_Pervasives_Native.Some (false
                                   ),uu____7723)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7786 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7802 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____7802
                    then
                      let uu____7803 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____7803 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7858)::uu____7859::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7922::(FStar_Pervasives_Native.Some (true
                                     ),uu____7923)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7986)::
                          (uu____7987,(arg,uu____7989))::[] ->
                          maybe_auto_squash arg
                      | (uu____8054,(arg,uu____8056))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8057)::[]
                          -> maybe_auto_squash arg
                      | uu____8122 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8138 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____8138
                       then
                         let uu____8139 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____8139 with
                         | uu____8194::(FStar_Pervasives_Native.Some (true
                                        ),uu____8195)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8258)::uu____8259::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8322)::
                             (uu____8323,(arg,uu____8325))::[] ->
                             maybe_auto_squash arg
                         | (uu____8390,(p,uu____8392))::(uu____8393,(q,uu____8395))::[]
                             ->
                             let uu____8460 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____8460
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8462 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8478 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____8478
                          then
                            let uu____8479 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____8479 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8534)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8573)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8612 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8628 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____8628
                             then
                               match args with
                               | (t,uu____8630)::[] ->
                                   let uu____8647 =
                                     let uu____8648 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____8648.FStar_Syntax_Syntax.n  in
                                   (match uu____8647 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8651::[],body,uu____8653) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8680 -> tm1)
                                    | uu____8683 -> tm1)
                               | (uu____8684,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8685))::
                                   (t,uu____8687)::[] ->
                                   let uu____8726 =
                                     let uu____8727 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____8727.FStar_Syntax_Syntax.n  in
                                   (match uu____8726 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8730::[],body,uu____8732) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8759 -> tm1)
                                    | uu____8762 -> tm1)
                               | uu____8763 -> tm1
                             else
                               (let uu____8773 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____8773
                                then
                                  match args with
                                  | (t,uu____8775)::[] ->
                                      let uu____8792 =
                                        let uu____8793 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____8793.FStar_Syntax_Syntax.n  in
                                      (match uu____8792 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8796::[],body,uu____8798)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8825 -> tm1)
                                       | uu____8828 -> tm1)
                                  | (uu____8829,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8830))::(t,uu____8832)::[] ->
                                      let uu____8871 =
                                        let uu____8872 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____8872.FStar_Syntax_Syntax.n  in
                                      (match uu____8871 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8875::[],body,uu____8877)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8904 -> tm1)
                                       | uu____8907 -> tm1)
                                  | uu____8908 -> tm1
                                else
                                  (let uu____8918 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____8918
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8919;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8920;_},uu____8921)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8938;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8939;_},uu____8940)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8957 -> tm1
                                   else
                                     (let uu____8967 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____8967 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8987 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8997;
                    FStar_Syntax_Syntax.vars = uu____8998;_},args)
                 ->
                 let uu____9020 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____9020
                 then
                   let uu____9021 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____9021 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9076)::
                        (uu____9077,(arg,uu____9079))::[] ->
                        maybe_auto_squash arg
                    | (uu____9144,(arg,uu____9146))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9147)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9212)::uu____9213::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9276::(FStar_Pervasives_Native.Some (false
                                   ),uu____9277)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9340 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9356 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9356
                    then
                      let uu____9357 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9357 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9412)::uu____9413::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9476::(FStar_Pervasives_Native.Some (true
                                     ),uu____9477)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9540)::
                          (uu____9541,(arg,uu____9543))::[] ->
                          maybe_auto_squash arg
                      | (uu____9608,(arg,uu____9610))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9611)::[]
                          -> maybe_auto_squash arg
                      | uu____9676 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9692 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9692
                       then
                         let uu____9693 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9693 with
                         | uu____9748::(FStar_Pervasives_Native.Some (true
                                        ),uu____9749)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9812)::uu____9813::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9876)::
                             (uu____9877,(arg,uu____9879))::[] ->
                             maybe_auto_squash arg
                         | (uu____9944,(p,uu____9946))::(uu____9947,(q,uu____9949))::[]
                             ->
                             let uu____10014 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____10014
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10016 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10032 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____10032
                          then
                            let uu____10033 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____10033 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10088)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10127)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10166 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10182 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____10182
                             then
                               match args with
                               | (t,uu____10184)::[] ->
                                   let uu____10201 =
                                     let uu____10202 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10202.FStar_Syntax_Syntax.n  in
                                   (match uu____10201 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10205::[],body,uu____10207) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10234 -> tm1)
                                    | uu____10237 -> tm1)
                               | (uu____10238,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10239))::
                                   (t,uu____10241)::[] ->
                                   let uu____10280 =
                                     let uu____10281 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10281.FStar_Syntax_Syntax.n  in
                                   (match uu____10280 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10284::[],body,uu____10286) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10313 -> tm1)
                                    | uu____10316 -> tm1)
                               | uu____10317 -> tm1
                             else
                               (let uu____10327 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10327
                                then
                                  match args with
                                  | (t,uu____10329)::[] ->
                                      let uu____10346 =
                                        let uu____10347 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10347.FStar_Syntax_Syntax.n  in
                                      (match uu____10346 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10350::[],body,uu____10352)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10379 -> tm1)
                                       | uu____10382 -> tm1)
                                  | (uu____10383,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10384))::(t,uu____10386)::[] ->
                                      let uu____10425 =
                                        let uu____10426 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10426.FStar_Syntax_Syntax.n  in
                                      (match uu____10425 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10429::[],body,uu____10431)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10458 -> tm1)
                                       | uu____10461 -> tm1)
                                  | uu____10462 -> tm1
                                else
                                  (let uu____10472 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10472
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10473;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10474;_},uu____10475)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10492;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10493;_},uu____10494)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10511 -> tm1
                                   else
                                     (let uu____10521 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10521 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10541 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____10556 -> tm1)
  
let maybe_simplify :
  'Auu____10563 'Auu____10564 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10564) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10563 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          (let uu____10607 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380")
              in
           if uu____10607
           then
             let uu____10608 = FStar_Syntax_Print.term_to_string tm  in
             let uu____10609 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10608 uu____10609
           else ());
          tm'
  
let is_norm_request :
  'Auu____10615 .
    FStar_Syntax_Syntax.term -> 'Auu____10615 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10628 =
        let uu____10635 =
          let uu____10636 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10636.FStar_Syntax_Syntax.n  in
        (uu____10635, args)  in
      match uu____10628 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10642::uu____10643::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10647::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10652::uu____10653::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10656 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___79_10667  ->
    match uu___79_10667 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10673 =
          let uu____10676 =
            let uu____10677 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10677  in
          [uu____10676]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10673
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10692 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10692) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10730 =
          let uu____10733 =
            let uu____10738 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step
               in
            uu____10738 s  in
          FStar_All.pipe_right uu____10733 FStar_Util.must  in
        FStar_All.pipe_right uu____10730 tr_norm_steps  in
      match args with
      | uu____10763::(tm,uu____10765)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____10788)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____10803)::uu____10804::(tm,uu____10806)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
            let uu____10846 =
              let uu____10849 = full_norm steps  in parse_steps uu____10849
               in
            Beta :: uu____10846  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____10858 -> failwith "Impossible"
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___80_10875  ->
    match uu___80_10875 with
    | (App
        (uu____10878,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10879;
                       FStar_Syntax_Syntax.vars = uu____10880;_},uu____10881,uu____10882))::uu____10883
        -> true
    | uu____10890 -> false
  
let firstn :
  'Auu____10896 .
    Prims.int ->
      'Auu____10896 Prims.list ->
        ('Auu____10896 Prims.list,'Auu____10896 Prims.list)
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
          (uu____10932,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10933;
                         FStar_Syntax_Syntax.vars = uu____10934;_},uu____10935,uu____10936))::uu____10937
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10944 -> false
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11091  ->
               let uu____11092 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11093 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11094 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11101 =
                 let uu____11102 =
                   let uu____11105 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11105
                    in
                 stack_to_string uu____11102  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11092 uu____11093 uu____11094 uu____11101);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11128 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11153 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11170 =
                 let uu____11171 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos  in
                 let uu____11172 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11171 uu____11172
                  in
               failwith uu____11170
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11173 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11190 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11191 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11192;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11193;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11196;
                 FStar_Syntax_Syntax.fv_delta = uu____11197;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11198;
                 FStar_Syntax_Syntax.fv_delta = uu____11199;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11200);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11208 = FStar_Syntax_Syntax.lid_of_fv fv  in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11208 ->
               let b = should_reify cfg stack  in
               (log cfg
                  (fun uu____11214  ->
                     let uu____11215 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____11216 = FStar_Util.string_of_bool b  in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11215 uu____11216);
                if b
                then
                  (let uu____11217 = FStar_List.tl stack  in
                   do_unfold_fv cfg env uu____11217 t1 fv)
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
                 let uu___115_11256 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11256.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11256.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11289 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____11289) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11297 = cfg  in
                 let uu____11298 =
                   FStar_List.filter
                     (fun uu___81_11301  ->
                        match uu___81_11301 with
                        | UnfoldOnly uu____11302 -> false
                        | NoDeltaSteps  -> false
                        | uu____11305 -> true) cfg.steps
                    in
                 {
                   steps = uu____11298;
                   tcenv = (uu___116_11297.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11297.primitive_steps);
                   strong = (uu___116_11297.strong);
                   memoize_lazy = (uu___116_11297.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11306 = get_norm_request (norm cfg' env []) args  in
               (match uu____11306 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11322 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11327  ->
                                match uu___82_11327 with
                                | UnfoldUntil uu____11328 -> true
                                | UnfoldOnly uu____11329 -> true
                                | uu____11332 -> false))
                         in
                      if uu____11322
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___117_11337 = cfg  in
                      {
                        steps = s;
                        tcenv = (uu___117_11337.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11337.primitive_steps);
                        strong = (uu___117_11337.strong);
                        memoize_lazy = (uu___117_11337.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      let uu____11344 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms")
                         in
                      if uu____11344
                      then
                        let uu____11347 =
                          let uu____11348 =
                            let uu____11353 = FStar_Util.now ()  in
                            (t1, uu____11353)  in
                          Debug uu____11348  in
                        uu____11347 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11357 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11357
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11364 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____11364
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11367 =
                      let uu____11374 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11374, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11367  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11387  ->
                         match uu___83_11387 with
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
                 let uu____11390 =
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
                 if uu____11390
                 then false
                 else
                   (let uu____11392 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11399  ->
                              match uu___84_11399 with
                              | UnfoldOnly uu____11400 -> true
                              | uu____11403 -> false))
                       in
                    match uu____11392 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11407 -> should_delta)
                  in
               (log cfg
                  (fun uu____11415  ->
                     let uu____11416 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____11417 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos
                        in
                     let uu____11418 =
                       FStar_Util.string_of_bool should_delta1  in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11416 uu____11417 uu____11418);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11421 = lookup_bvar env x  in
               (match uu____11421 with
                | Univ uu____11424 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11473 = FStar_ST.op_Bang r  in
                      (match uu____11473 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11591  ->
                                 let uu____11592 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____11593 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11592
                                   uu____11593);
                            (let uu____11594 =
                               let uu____11595 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____11595.FStar_Syntax_Syntax.n  in
                             match uu____11594 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11598 ->
                                 norm cfg env2 stack t'
                             | uu____11615 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11685)::uu____11686 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11695)::uu____11696 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11706,uu____11707))::stack_rest ->
                    (match c with
                     | Univ uu____11711 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11720 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11741  ->
                                    let uu____11742 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11742);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11782  ->
                                    let uu____11783 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11783);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____11861  ->
                          let uu____11862 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11862);
                     norm cfg env stack1 t1)
                | (Debug uu____11863)::uu____11864 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11871 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11871
                    else
                      (let uu____11873 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11873 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11915  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11943 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____11943
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11953 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11953)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_11958 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_11958.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_11958.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11959 -> lopt  in
                           (log cfg
                              (fun uu____11965  ->
                                 let uu____11966 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11966);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_11975 = cfg  in
                               {
                                 steps = (uu___119_11975.steps);
                                 tcenv = (uu___119_11975.tcenv);
                                 delta_level = (uu___119_11975.delta_level);
                                 primitive_steps =
                                   (uu___119_11975.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_11975.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_11975.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11986)::uu____11987 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11994 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11994
                    else
                      (let uu____11996 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11996 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12038  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12066 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12066
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12076 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12076)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12081 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12081.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12081.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12082 -> lopt  in
                           (log cfg
                              (fun uu____12088  ->
                                 let uu____12089 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12089);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12098 = cfg  in
                               {
                                 steps = (uu___119_12098.steps);
                                 tcenv = (uu___119_12098.tcenv);
                                 delta_level = (uu___119_12098.delta_level);
                                 primitive_steps =
                                   (uu___119_12098.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12098.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12098.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12109)::uu____12110 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12121 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12121
                    else
                      (let uu____12123 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12123 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12165  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12193 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12193
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12203 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12203)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12208 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12208.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12208.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12209 -> lopt  in
                           (log cfg
                              (fun uu____12215  ->
                                 let uu____12216 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12216);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12225 = cfg  in
                               {
                                 steps = (uu___119_12225.steps);
                                 tcenv = (uu___119_12225.tcenv);
                                 delta_level = (uu___119_12225.delta_level);
                                 primitive_steps =
                                   (uu___119_12225.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12225.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12225.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12236)::uu____12237 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12248 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12248
                    else
                      (let uu____12250 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12250 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12292  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12320 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12320
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12330 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12330)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12335 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12335.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12335.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12336 -> lopt  in
                           (log cfg
                              (fun uu____12342  ->
                                 let uu____12343 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12343);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12352 = cfg  in
                               {
                                 steps = (uu___119_12352.steps);
                                 tcenv = (uu___119_12352.tcenv);
                                 delta_level = (uu___119_12352.delta_level);
                                 primitive_steps =
                                   (uu___119_12352.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12352.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12352.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12363)::uu____12364 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12379 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12379
                    else
                      (let uu____12381 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12381 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12423  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12451 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12451
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12461 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12461)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12466 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12466.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12466.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12467 -> lopt  in
                           (log cfg
                              (fun uu____12473  ->
                                 let uu____12474 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12474);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12483 = cfg  in
                               {
                                 steps = (uu___119_12483.steps);
                                 tcenv = (uu___119_12483.tcenv);
                                 delta_level = (uu___119_12483.delta_level);
                                 primitive_steps =
                                   (uu___119_12483.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12483.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12483.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12494 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12494
                    else
                      (let uu____12496 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12496 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12538  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12566 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12566
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12576 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12576)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12581 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12581.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12581.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12582 -> lopt  in
                           (log cfg
                              (fun uu____12588  ->
                                 let uu____12589 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12589);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12598 = cfg  in
                               {
                                 steps = (uu___119_12598.steps);
                                 tcenv = (uu___119_12598.tcenv);
                                 delta_level = (uu___119_12598.delta_level);
                                 primitive_steps =
                                   (uu___119_12598.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12598.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12598.normalize_pure_lets)
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
                      (fun uu____12647  ->
                         fun stack1  ->
                           match uu____12647 with
                           | (a,aq) ->
                               let uu____12659 =
                                 let uu____12660 =
                                   let uu____12667 =
                                     let uu____12668 =
                                       let uu____12699 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12699, false)  in
                                     Clos uu____12668  in
                                   (uu____12667, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12660  in
                               uu____12659 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12783  ->
                     let uu____12784 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12784);
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
                             ((let uu___120_12820 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_12820.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_12820.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12821 ->
                      let uu____12826 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12826)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12829 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12829 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12860 =
                          let uu____12861 =
                            let uu____12868 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___121_12870 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_12870.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_12870.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12868)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12861  in
                        mk uu____12860 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12889 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12889
               else
                 (let uu____12891 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12891 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12899 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12923  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12899 c1  in
                      let t2 =
                        let uu____12945 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12945 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13004)::uu____13005 ->
                    (log cfg
                       (fun uu____13016  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13017)::uu____13018 ->
                    (log cfg
                       (fun uu____13029  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13030,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13031;
                                   FStar_Syntax_Syntax.vars = uu____13032;_},uu____13033,uu____13034))::uu____13035
                    ->
                    (log cfg
                       (fun uu____13044  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13045)::uu____13046 ->
                    (log cfg
                       (fun uu____13057  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13058 ->
                    (log cfg
                       (fun uu____13061  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13065  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13082 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13082
                         | FStar_Util.Inr c ->
                             let uu____13090 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13090
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13103 =
                               let uu____13104 =
                                 let uu____13131 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13131, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13104
                                in
                             mk uu____13103 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____13150 ->
                           let uu____13151 =
                             let uu____13152 =
                               let uu____13153 =
                                 let uu____13180 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13180, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13153
                                in
                             mk uu____13152 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____13151))))
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
                         let uu____13290 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13290 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13310 = cfg  in
                               let uu____13311 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___122_13310.steps);
                                 tcenv = uu____13311;
                                 delta_level = (uu___122_13310.delta_level);
                                 primitive_steps =
                                   (uu___122_13310.primitive_steps);
                                 strong = (uu___122_13310.strong);
                                 memoize_lazy = (uu___122_13310.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___122_13310.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____13316 =
                                 let uu____13317 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13317  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13316
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___123_13320 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13320.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13320.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             }))
                  in
               let uu____13321 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13321
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13332,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13333;
                               FStar_Syntax_Syntax.lbunivs = uu____13334;
                               FStar_Syntax_Syntax.lbtyp = uu____13335;
                               FStar_Syntax_Syntax.lbeff = uu____13336;
                               FStar_Syntax_Syntax.lbdef = uu____13337;_}::uu____13338),uu____13339)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____13375 =
                 (let uu____13378 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____13378) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13380 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)
                             in
                          Prims.op_Negation uu____13380)))
                  in
               if uu____13375
               then
                 let binder =
                   let uu____13382 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13382  in
                 let env1 =
                   let uu____13392 =
                     let uu____13399 =
                       let uu____13400 =
                         let uu____13431 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13431,
                           false)
                          in
                       Clos uu____13400  in
                     ((FStar_Pervasives_Native.Some binder), uu____13399)  in
                   uu____13392 :: env  in
                 (log cfg
                    (fun uu____13524  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13526 =
                    let uu____13531 =
                      let uu____13532 =
                        let uu____13533 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left
                           in
                        FStar_All.pipe_right uu____13533
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [uu____13532]  in
                    FStar_Syntax_Subst.open_term uu____13531 body  in
                  match uu____13526 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13542  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let lbname =
                          let x =
                            let uu____13550 = FStar_List.hd bs  in
                            FStar_Pervasives_Native.fst uu____13550  in
                          FStar_Util.Inl
                            (let uu___124_13560 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_13560.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_13560.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             })
                           in
                        log cfg
                          (fun uu____13563  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___125_13565 = lb  in
                           let uu____13566 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_13565.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_13565.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13566
                           }  in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13601  -> dummy :: env1) env)
                            in
                         let stack1 = (Cfg cfg) :: stack  in
                         let cfg1 =
                           let uu___126_13624 = cfg  in
                           {
                             steps = (uu___126_13624.steps);
                             tcenv = (uu___126_13624.tcenv);
                             delta_level = (uu___126_13624.delta_level);
                             primitive_steps =
                               (uu___126_13624.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___126_13624.memoize_lazy);
                             normalize_pure_lets =
                               (uu___126_13624.normalize_pure_lets)
                           }  in
                         log cfg1
                           (fun uu____13627  ->
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
               let uu____13644 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13644 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13680 =
                               let uu___127_13681 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13681.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13681.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13680  in
                           let uu____13682 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13682 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13708 =
                                   FStar_List.map (fun uu____13724  -> dummy)
                                     lbs1
                                    in
                                 let uu____13725 =
                                   let uu____13734 =
                                     FStar_List.map
                                       (fun uu____13754  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13734 env  in
                                 FStar_List.append uu____13708 uu____13725
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13778 =
                                       let uu___128_13779 = rc  in
                                       let uu____13780 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_13779.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13780;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_13779.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13778
                                 | uu____13787 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___129_13791 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_13791.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_13791.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
                      let uu____13801 =
                        FStar_List.map (fun uu____13817  -> dummy) lbs2  in
                      FStar_List.append uu____13801 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13825 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13825 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_13841 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_13841.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_13841.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13868 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13868
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13887 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13963  ->
                        match uu____13963 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14084 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14084.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14084.FStar_Syntax_Syntax.sort)
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
               (match uu____13887 with
                | (rec_env,memos,uu____14297) ->
                    let uu____14350 =
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
                             let uu____14661 =
                               let uu____14668 =
                                 let uu____14669 =
                                   let uu____14700 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14700, false)
                                    in
                                 Clos uu____14669  in
                               (FStar_Pervasives_Native.None, uu____14668)
                                in
                             uu____14661 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14810  ->
                     let uu____14811 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14811);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14833 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14835::uu____14836 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14841) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14842 ->
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
                             | uu____14873 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14887 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14887
                              | uu____14898 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2))))

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
              let uu____14910 = FStar_Syntax_Syntax.range_of_fv f  in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14910  in
            let uu____14911 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            match uu____14911 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14924  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14935  ->
                      let uu____14936 = FStar_Syntax_Print.term_to_string t0
                         in
                      let uu____14937 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14936
                        uu____14937);
                 (let t1 =
                    let uu____14939 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____14941 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac)
                            in
                         Prims.op_Negation uu____14941)
                       in
                    if uu____14939
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
                    | (UnivArgs (us',uu____14951))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env)
                           in
                        norm cfg env1 stack1 t1
                    | uu____15006 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15009 ->
                        let uu____15012 =
                          let uu____15013 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15013
                           in
                        failwith uu____15012
                  else norm cfg env stack t1))

and (reduce_impure_comp :
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
                let uu____15034 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations)
                   in
                if uu____15034
                then
                  let uu___132_15035 = cfg  in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_15035.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_15035.primitive_steps);
                    strong = (uu___132_15035.strong);
                    memoize_lazy = (uu___132_15035.memoize_lazy);
                    normalize_pure_lets =
                      (uu___132_15035.normalize_pure_lets)
                  }
                else
                  (let uu___133_15037 = cfg  in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_15037.tcenv);
                     delta_level = (uu___133_15037.delta_level);
                     primitive_steps = (uu___133_15037.primitive_steps);
                     strong = (uu___133_15037.strong);
                     memoize_lazy = (uu___133_15037.memoize_lazy);
                     normalize_pure_lets =
                       (uu___133_15037.normalize_pure_lets)
                   })
                 in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head2 = FStar_Syntax_Util.unascribe head1  in
                log cfg
                  (fun uu____15066  ->
                     let uu____15067 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____15068 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15067
                       uu____15068);
                (let uu____15069 =
                   let uu____15070 = FStar_Syntax_Subst.compress head2  in
                   uu____15070.FStar_Syntax_Syntax.n  in
                 match uu____15069 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____15088 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15088 with
                      | (uu____15089,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15095 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15103 =
                                   let uu____15104 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____15104.FStar_Syntax_Syntax.n  in
                                 match uu____15103 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15110,uu____15111))
                                     ->
                                     let uu____15120 =
                                       let uu____15121 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____15121.FStar_Syntax_Syntax.n  in
                                     (match uu____15120 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15127,msrc,uu____15129))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15138 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15138
                                      | uu____15139 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15140 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____15141 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____15141 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15146 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15146.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15146.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15146.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      }  in
                                    let uu____15147 = FStar_List.tl stack  in
                                    let uu____15148 =
                                      let uu____15149 =
                                        let uu____15152 =
                                          let uu____15153 =
                                            let uu____15166 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____15166)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15153
                                           in
                                        FStar_Syntax_Syntax.mk uu____15152
                                         in
                                      uu____15149
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____15147 uu____15148
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15182 =
                                      let uu____15183 = is_return body  in
                                      match uu____15183 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15187;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15188;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15193 -> false  in
                                    if uu____15182
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos  in
                                       let head3 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef
                                          in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body
                                          in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         }  in
                                       let body2 =
                                         let uu____15216 =
                                           let uu____15219 =
                                             let uu____15220 =
                                               let uu____15237 =
                                                 let uu____15240 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____15240]  in
                                               (uu____15237, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15220
                                              in
                                           FStar_Syntax_Syntax.mk uu____15219
                                            in
                                         uu____15216
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____15256 =
                                           let uu____15257 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____15257.FStar_Syntax_Syntax.n
                                            in
                                         match uu____15256 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15263::uu____15264::[])
                                             ->
                                             let uu____15271 =
                                               let uu____15274 =
                                                 let uu____15275 =
                                                   let uu____15282 =
                                                     let uu____15285 =
                                                       let uu____15286 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15286
                                                        in
                                                     let uu____15287 =
                                                       let uu____15290 =
                                                         let uu____15291 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15291
                                                          in
                                                       [uu____15290]  in
                                                     uu____15285 ::
                                                       uu____15287
                                                      in
                                                   (bind1, uu____15282)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15275
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15274
                                                in
                                             uu____15271
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15299 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____15305 =
                                           let uu____15308 =
                                             let uu____15309 =
                                               let uu____15324 =
                                                 let uu____15327 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____15328 =
                                                   let uu____15331 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____15332 =
                                                     let uu____15335 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____15336 =
                                                       let uu____15339 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____15340 =
                                                         let uu____15343 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____15344 =
                                                           let uu____15347 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____15347]  in
                                                         uu____15343 ::
                                                           uu____15344
                                                          in
                                                       uu____15339 ::
                                                         uu____15340
                                                        in
                                                     uu____15335 ::
                                                       uu____15336
                                                      in
                                                   uu____15331 :: uu____15332
                                                    in
                                                 uu____15327 :: uu____15328
                                                  in
                                               (bind_inst, uu____15324)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15309
                                              in
                                           FStar_Syntax_Syntax.mk uu____15308
                                            in
                                         uu____15305
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____15358  ->
                                            let uu____15359 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15359);
                                       (let uu____15360 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____15360 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____15384 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15384 with
                      | (uu____15385,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15420 =
                                  let uu____15421 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15421.FStar_Syntax_Syntax.n  in
                                match uu____15420 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15427) -> t2
                                | uu____15432 -> head3  in
                              let uu____15433 =
                                let uu____15434 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15434.FStar_Syntax_Syntax.n  in
                              match uu____15433 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15440 -> FStar_Pervasives_Native.None
                               in
                            let uu____15441 = maybe_extract_fv head3  in
                            match uu____15441 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15451 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15451
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____15456 = maybe_extract_fv head4
                                     in
                                  match uu____15456 with
                                  | FStar_Pervasives_Native.Some uu____15461
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15462 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____15467 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15482 =
                              match uu____15482 with
                              | (e,q) ->
                                  let uu____15489 =
                                    let uu____15490 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15490.FStar_Syntax_Syntax.n  in
                                  (match uu____15489 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15505 -> false)
                               in
                            let uu____15506 =
                              let uu____15507 =
                                let uu____15514 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15514 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15507
                               in
                            if uu____15506
                            then
                              let uu____15519 =
                                let uu____15520 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15520
                                 in
                              failwith uu____15519
                            else ());
                           (let uu____15522 = maybe_unfold_action head_app
                               in
                            match uu____15522 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos
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
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body
                                   in
                                let uu____15559 = FStar_List.tl stack  in
                                norm cfg env uu____15559 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15561) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15585 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15585  in
                     (log cfg
                        (fun uu____15589  ->
                           let uu____15590 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15590);
                      (let uu____15591 = FStar_List.tl stack  in
                       norm cfg env uu____15591 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15593) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15718  ->
                               match uu____15718 with
                               | (pat,wopt,tm) ->
                                   let uu____15766 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15766)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____15798 = FStar_List.tl stack  in
                     norm cfg env uu____15798 tm
                 | uu____15799 -> fallback ())

and (reify_lift :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv  in
            log cfg
              (fun uu____15813  ->
                 let uu____15814 = FStar_Ident.string_of_lid msrc  in
                 let uu____15815 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15816 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15814
                   uu____15815 uu____15816);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____15818 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15818 with
               | (uu____15819,return_repr) ->
                   let return_inst =
                     let uu____15828 =
                       let uu____15829 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15829.FStar_Syntax_Syntax.n  in
                     match uu____15828 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15835::[]) ->
                         let uu____15842 =
                           let uu____15845 =
                             let uu____15846 =
                               let uu____15853 =
                                 let uu____15856 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15856]  in
                               (return_tm, uu____15853)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15846  in
                           FStar_Syntax_Syntax.mk uu____15845  in
                         uu____15842 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15864 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15867 =
                     let uu____15870 =
                       let uu____15871 =
                         let uu____15886 =
                           let uu____15889 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15890 =
                             let uu____15893 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15893]  in
                           uu____15889 :: uu____15890  in
                         (return_inst, uu____15886)  in
                       FStar_Syntax_Syntax.Tm_app uu____15871  in
                     FStar_Syntax_Syntax.mk uu____15870  in
                   uu____15867 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15902 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____15902 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15905 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____15905
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15906;
                     FStar_TypeChecker_Env.mtarget = uu____15907;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15908;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____15923 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____15923
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15924;
                     FStar_TypeChecker_Env.mtarget = uu____15925;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15926;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15950 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____15951 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____15950 t FStar_Syntax_Syntax.tun uu____15951)

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
                (fun uu____16007  ->
                   match uu____16007 with
                   | (a,imp) ->
                       let uu____16018 = norm cfg env [] a  in
                       (uu____16018, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_16032 = comp  in
            let uu____16033 =
              let uu____16034 =
                let uu____16043 = norm cfg env [] t  in
                let uu____16044 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____16043, uu____16044)  in
              FStar_Syntax_Syntax.Total uu____16034  in
            {
              FStar_Syntax_Syntax.n = uu____16033;
              FStar_Syntax_Syntax.pos =
                (uu___135_16032.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_16032.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_16059 = comp  in
            let uu____16060 =
              let uu____16061 =
                let uu____16070 = norm cfg env [] t  in
                let uu____16071 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____16070, uu____16071)  in
              FStar_Syntax_Syntax.GTotal uu____16061  in
            {
              FStar_Syntax_Syntax.n = uu____16060;
              FStar_Syntax_Syntax.pos =
                (uu___136_16059.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16059.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16123  ->
                      match uu____16123 with
                      | (a,i) ->
                          let uu____16134 = norm cfg env [] a  in
                          (uu____16134, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16145  ->
                      match uu___85_16145 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16149 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____16149
                      | f -> f))
               in
            let uu___137_16153 = comp  in
            let uu____16154 =
              let uu____16155 =
                let uu___138_16156 = ct  in
                let uu____16157 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____16158 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____16161 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16157;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16156.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16158;
                  FStar_Syntax_Syntax.effect_args = uu____16161;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____16155  in
            {
              FStar_Syntax_Syntax.n = uu____16154;
              FStar_Syntax_Syntax.pos =
                (uu___137_16153.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16153.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____16172  ->
        match uu____16172 with
        | (x,imp) ->
            let uu____16175 =
              let uu___139_16176 = x  in
              let uu____16177 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16176.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16176.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16177
              }  in
            (uu____16175, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16183 =
          FStar_List.fold_left
            (fun uu____16201  ->
               fun b  ->
                 match uu____16201 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16183 with | (nbs,uu____16241) -> FStar_List.rev nbs

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
            let uu____16257 =
              let uu___140_16258 = rc  in
              let uu____16259 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16258.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16259;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16258.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16257
        | uu____16266 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16279  ->
               let uu____16280 = FStar_Syntax_Print.tag_of_term t  in
               let uu____16281 = FStar_Syntax_Print.term_to_string t  in
               let uu____16282 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____16289 =
                 let uu____16290 =
                   let uu____16293 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16293
                    in
                 stack_to_string uu____16290  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16280 uu____16281 uu____16282 uu____16289);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16323 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms")
                    in
                 if uu____16323
                 then
                   let time_now = FStar_Util.now ()  in
                   let uu____16325 =
                     let uu____16326 =
                       let uu____16327 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____16327  in
                     FStar_Util.string_of_int uu____16326  in
                   let uu____16332 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____16333 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16325 uu____16332 uu____16333
                 else ());
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____16387  ->
                     let uu____16388 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16388);
                rebuild cfg env stack1 t1)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env' stack1 t2
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs  in
               let lopt1 = norm_lcomp_opt cfg env'' lopt  in
               let uu____16424 =
                 let uu___141_16425 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16425.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16425.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____16424
           | (Arg (Univ uu____16426,uu____16427,uu____16428))::uu____16429 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16432,uu____16433))::uu____16434 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____16450),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16503  ->
                     let uu____16504 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16504);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm  in
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t2
                   else
                     (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____16514 = FStar_ST.op_Bang m  in
                   match uu____16514 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm  in
                         let t2 =
                           FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                             FStar_Pervasives_Native.None r
                            in
                         rebuild cfg env_arg stack1 t2
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____16651,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____16698 =
                 log cfg
                   (fun uu____16702  ->
                      let uu____16703 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16703);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____16707 =
                 let uu____16708 = FStar_Syntax_Subst.compress t1  in
                 uu____16708.FStar_Syntax_Syntax.n  in
               (match uu____16707 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16735 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____16735  in
                    (log cfg
                       (fun uu____16739  ->
                          let uu____16740 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16740);
                     (let uu____16741 = FStar_List.tl stack  in
                      norm cfg env1 uu____16741 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16742);
                       FStar_Syntax_Syntax.pos = uu____16743;
                       FStar_Syntax_Syntax.vars = uu____16744;_},(e,uu____16746)::[])
                    -> norm cfg env1 stack' e
                | uu____16775 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16795  ->
                     let uu____16796 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16796);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____16801 =
                   log cfg
                     (fun uu____16806  ->
                        let uu____16807 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____16808 =
                          let uu____16809 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16826  ->
                                    match uu____16826 with
                                    | (p,uu____16836,uu____16837) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____16809
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16807 uu____16808);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps)
                       in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_16854  ->
                                match uu___86_16854 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16855 -> false))
                         in
                      let steps' = [Exclude Zeta]  in
                      let uu___142_16859 = cfg  in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_16859.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_16859.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_16859.memoize_lazy);
                        normalize_pure_lets =
                          (uu___142_16859.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16891 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16912 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16972  ->
                                    fun uu____16973  ->
                                      match (uu____16972, uu____16973) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17064 = norm_pat env3 p1
                                             in
                                          (match uu____17064 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____16912 with
                           | (pats1,env3) ->
                               ((let uu___143_17146 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17146.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17165 = x  in
                            let uu____17166 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17165.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17165.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17166
                            }  in
                          ((let uu___145_17180 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17180.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17191 = x  in
                            let uu____17192 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17191.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17191.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17192
                            }  in
                          ((let uu___147_17206 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17206.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___148_17222 = x  in
                            let uu____17223 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17222.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17222.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17223
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___149_17230 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17230.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17240 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17254 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____17254 with
                                  | (p,wopt,e) ->
                                      let uu____17274 = norm_pat env1 p  in
                                      (match uu____17274 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17299 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17299
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____17305 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____17305)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17315) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17320 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17321;
                         FStar_Syntax_Syntax.fv_delta = uu____17322;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17323;
                         FStar_Syntax_Syntax.fv_delta = uu____17324;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17325);_}
                       -> true
                   | uu____17332 -> false  in
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
                   let uu____17477 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____17477 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17564 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17603 ->
                                 let uu____17604 =
                                   let uu____17605 = is_cons head1  in
                                   Prims.op_Negation uu____17605  in
                                 FStar_Util.Inr uu____17604)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17630 =
                              let uu____17631 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____17631.FStar_Syntax_Syntax.n  in
                            (match uu____17630 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17649 ->
                                 let uu____17650 =
                                   let uu____17651 = is_cons head1  in
                                   Prims.op_Negation uu____17651  in
                                 FStar_Util.Inr uu____17650))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____17720)::rest_a,(p1,uu____17723)::rest_p) ->
                       let uu____17767 = matches_pat t2 p1  in
                       (match uu____17767 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17816 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17922 = matches_pat scrutinee1 p1  in
                       (match uu____17922 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17962  ->
                                  let uu____17963 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____17964 =
                                    let uu____17965 =
                                      FStar_List.map
                                        (fun uu____17975  ->
                                           match uu____17975 with
                                           | (uu____17980,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____17965
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17963 uu____17964);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18011  ->
                                       match uu____18011 with
                                       | (bv,t2) ->
                                           let uu____18034 =
                                             let uu____18041 =
                                               let uu____18044 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____18044
                                                in
                                             let uu____18045 =
                                               let uu____18046 =
                                                 let uu____18077 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____18077, false)
                                                  in
                                               Clos uu____18046  in
                                             (uu____18041, uu____18045)  in
                                           uu____18034 :: env2) env1 s
                                 in
                              let uu____18194 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____18194)))
                    in
                 let uu____18195 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota))
                    in
                 if uu____18195
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18216  ->
                match uu___87_18216 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18220 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18226 -> d  in
      let uu____18229 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18231 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations)
              in
           Prims.op_Negation uu____18231)
         in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18229
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
            let uu___150_18256 = config s e  in
            {
              steps = (uu___150_18256.steps);
              tcenv = (uu___150_18256.tcenv);
              delta_level = (uu___150_18256.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18256.strong);
              memoize_lazy = (uu___150_18256.memoize_lazy);
              normalize_pure_lets = (uu___150_18256.normalize_pure_lets)
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
      fun t  -> let uu____18281 = config s e  in norm_comp uu____18281 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____18294 = config [] env  in norm_universe uu____18294 [] u
  
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
        let uu____18312 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____18312  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18319 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18338 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18338.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18338.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____18345 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____18345
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
                  let uu___152_18354 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18354.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18354.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18354.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___153_18356 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18356.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18356.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18356.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18356.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___154_18357 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18357.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18357.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18359 -> c
  
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
        let uu____18371 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____18371  in
      let uu____18378 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____18378
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18382  ->
                 let uu____18383 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____18383)
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
            ((let uu____18400 =
                let uu____18405 =
                  let uu____18406 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18406
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____18405)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18400);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18417 = config [AllowUnboundUniverses] env  in
          norm_comp uu____18417 [] c
        with
        | e ->
            ((let uu____18430 =
                let uu____18435 =
                  let uu____18436 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18436
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____18435)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18430);
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
                   let uu____18473 =
                     let uu____18474 =
                       let uu____18481 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____18481)  in
                     FStar_Syntax_Syntax.Tm_refine uu____18474  in
                   mk uu____18473 t01.FStar_Syntax_Syntax.pos
               | uu____18486 -> t2)
          | uu____18487 -> t2  in
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
        let uu____18527 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____18527 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18556 ->
                 let uu____18563 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____18563 with
                  | (actuals,uu____18573,uu____18574) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18588 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____18588 with
                         | (binders,args) ->
                             let uu____18605 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____18605
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
      | uu____18613 ->
          let uu____18614 = FStar_Syntax_Util.head_and_args t  in
          (match uu____18614 with
           | (head1,args) ->
               let uu____18651 =
                 let uu____18652 = FStar_Syntax_Subst.compress head1  in
                 uu____18652.FStar_Syntax_Syntax.n  in
               (match uu____18651 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18655,thead) ->
                    let uu____18681 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____18681 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18723 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18731 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18731.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18731.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18731.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18731.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18731.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18731.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18731.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18731.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18731.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18731.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18731.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18731.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18731.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18731.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18731.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18731.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18731.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18731.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18731.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18731.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18731.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18731.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18731.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18731.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18731.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18731.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18731.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18731.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18731.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18731.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18731.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____18723 with
                            | (uu____18732,ty,uu____18734) ->
                                eta_expand_with_type env t ty))
                | uu____18735 ->
                    let uu____18736 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18744 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18744.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18744.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18744.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18744.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18744.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18744.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18744.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18744.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18744.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18744.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18744.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18744.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18744.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18744.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18744.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18744.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18744.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18744.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18744.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18744.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18744.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18744.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18744.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18744.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18744.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18744.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18744.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18744.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18744.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18744.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18744.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____18736 with
                     | (uu____18745,ty,uu____18747) ->
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
            | (uu____18821,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18827,FStar_Util.Inl t) ->
                let uu____18833 =
                  let uu____18836 =
                    let uu____18837 =
                      let uu____18850 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____18850)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____18837  in
                  FStar_Syntax_Syntax.mk uu____18836  in
                uu____18833 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____18854 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____18854 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let uu____18881 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18936 ->
                    let uu____18937 =
                      let uu____18946 =
                        let uu____18947 = FStar_Syntax_Subst.compress t3  in
                        uu____18947.FStar_Syntax_Syntax.n  in
                      (uu____18946, tc)  in
                    (match uu____18937 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18972) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19009) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19048,FStar_Util.Inl uu____19049) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19072 -> failwith "Impossible")
                 in
              (match uu____18881 with
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
          let uu____19177 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____19177 with
          | (univ_names1,binders1,tc) ->
              let uu____19235 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____19235)
  
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
          let uu____19270 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____19270 with
          | (univ_names1,binders1,tc) ->
              let uu____19330 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____19330)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19363 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____19363 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19391 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19391.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19391.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19391.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19391.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19412 = s  in
          let uu____19413 =
            let uu____19414 =
              let uu____19423 = FStar_List.map (elim_uvars env) sigs  in
              (uu____19423, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____19414  in
          {
            FStar_Syntax_Syntax.sigel = uu____19413;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19412.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19412.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19412.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19412.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19440 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____19440 with
           | (univ_names1,uu____19458,typ1) ->
               let uu___163_19472 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19472.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19472.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19472.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19472.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19478 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____19478 with
           | (univ_names1,uu____19496,typ1) ->
               let uu___164_19510 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19510.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19510.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19510.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19510.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19544 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____19544 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19567 =
                            let uu____19568 =
                              FStar_Syntax_Subst.subst opening t  in
                            remove_uvar_solutions env uu____19568  in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19567
                           in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___165_19571 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19571.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19571.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        }))
             in
          let uu___166_19572 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19572.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19572.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19572.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19572.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19584 = s  in
          let uu____19585 =
            let uu____19586 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____19586  in
          {
            FStar_Syntax_Syntax.sigel = uu____19585;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19584.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19584.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19584.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19584.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19590 = elim_uvars_aux_t env us [] t  in
          (match uu____19590 with
           | (us1,uu____19608,t1) ->
               let uu___168_19622 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19622.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19622.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19622.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19622.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19623 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19625 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____19625 with
           | (univs1,binders,signature) ->
               let uu____19653 =
                 let uu____19662 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____19662 with
                 | (univs_opening,univs2) ->
                     let uu____19689 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____19689)
                  in
               (match uu____19653 with
                | (univs_opening,univs_closing) ->
                    let uu____19706 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____19712 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____19713 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____19712, uu____19713)  in
                    (match uu____19706 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____19735 =
                           match uu____19735 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____19753 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____19753 with
                                | (us1,t1) ->
                                    let uu____19764 =
                                      let uu____19769 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____19776 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____19769, uu____19776)  in
                                    (match uu____19764 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19789 =
                                           let uu____19794 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____19803 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____19794, uu____19803)  in
                                         (match uu____19789 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19819 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19819
                                                 in
                                              let uu____19820 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____19820 with
                                               | (uu____19841,uu____19842,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19857 =
                                                       let uu____19858 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19858
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19857
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____19863 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____19863 with
                           | (uu____19876,uu____19877,t1) -> t1  in
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
                             | uu____19937 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____19954 =
                               let uu____19955 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____19955.FStar_Syntax_Syntax.n  in
                             match uu____19954 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20014 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____20043 =
                               let uu____20044 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____20044.FStar_Syntax_Syntax.n  in
                             match uu____20043 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20065) ->
                                 let uu____20086 = destruct_action_body body
                                    in
                                 (match uu____20086 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20131 ->
                                 let uu____20132 = destruct_action_body t  in
                                 (match uu____20132 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____20181 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____20181 with
                           | (action_univs,t) ->
                               let uu____20190 = destruct_action_typ_templ t
                                  in
                               (match uu____20190 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20231 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20231.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20231.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___170_20233 = ed  in
                           let uu____20234 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____20235 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____20236 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____20237 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____20238 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____20239 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____20240 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____20241 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____20242 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____20243 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____20244 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____20245 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____20246 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____20247 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20233.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20233.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20234;
                             FStar_Syntax_Syntax.bind_wp = uu____20235;
                             FStar_Syntax_Syntax.if_then_else = uu____20236;
                             FStar_Syntax_Syntax.ite_wp = uu____20237;
                             FStar_Syntax_Syntax.stronger = uu____20238;
                             FStar_Syntax_Syntax.close_wp = uu____20239;
                             FStar_Syntax_Syntax.assert_p = uu____20240;
                             FStar_Syntax_Syntax.assume_p = uu____20241;
                             FStar_Syntax_Syntax.null_wp = uu____20242;
                             FStar_Syntax_Syntax.trivial = uu____20243;
                             FStar_Syntax_Syntax.repr = uu____20244;
                             FStar_Syntax_Syntax.return_repr = uu____20245;
                             FStar_Syntax_Syntax.bind_repr = uu____20246;
                             FStar_Syntax_Syntax.actions = uu____20247
                           }  in
                         let uu___171_20250 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20250.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20250.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20250.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20250.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20267 =
            match uu___88_20267 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20294 = elim_uvars_aux_t env us [] t  in
                (match uu____20294 with
                 | (us1,uu____20318,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___172_20337 = sub_eff  in
            let uu____20338 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____20341 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20337.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20337.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20338;
              FStar_Syntax_Syntax.lift = uu____20341
            }  in
          let uu___173_20344 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20344.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20344.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20344.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20344.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20354 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____20354 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20388 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20388.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20388.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20388.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20388.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20399 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  