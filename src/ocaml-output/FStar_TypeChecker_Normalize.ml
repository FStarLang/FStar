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
  | Unmeta 
  | Unascribe [@@deriving show]
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
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____138 -> false
  
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____172  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____373 -> false
  
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
    match projectee with | Univ _0 -> true | uu____475 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____486 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___72_505  ->
    match uu___72_505 with
    | Clos (uu____506,t,uu____508,uu____509) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____554 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____834 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____870 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____906 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____975 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1017 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1073 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1113 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1145 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1181 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1197 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____1222 .
    'Auu____1222 ->
      FStar_Range.range -> 'Auu____1222 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1276 = FStar_ST.op_Bang r  in
          match uu____1276 with
          | FStar_Pervasives_Native.Some uu____1324 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____1378 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____1378 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___73_1385  ->
    match uu___73_1385 with
    | Arg (c,uu____1387,uu____1388) ->
        let uu____1389 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1389
    | MemoLazy uu____1390 -> "MemoLazy"
    | Abs (uu____1397,bs,uu____1399,uu____1400,uu____1401) ->
        let uu____1406 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1406
    | UnivArgs uu____1411 -> "UnivArgs"
    | Match uu____1418 -> "Match"
    | App (uu____1425,t,uu____1427,uu____1428) ->
        let uu____1429 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1429
    | Meta (m,uu____1431) -> "Meta"
    | Let uu____1432 -> "Let"
    | Cfg uu____1441 -> "Cfg"
    | Debug (t,uu____1443) ->
        let uu____1444 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1444
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1452 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1452 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1468 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____1468 then f () else ()
  
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1481 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops"))
         in
      if uu____1481 then f () else ()
  
let is_empty : 'Auu____1485 . 'Auu____1485 Prims.list -> Prims.bool =
  fun uu___74_1491  ->
    match uu___74_1491 with | [] -> true | uu____1494 -> false
  
let lookup_bvar :
  'Auu____1501 'Auu____1502 .
    ('Auu____1502,'Auu____1501) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1501
  =
  fun env  ->
    fun x  ->
      try
        let uu____1526 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____1526
      with
      | uu____1539 ->
          let uu____1540 =
            let uu____1541 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____1541  in
          failwith uu____1540
  
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
          let uu____1578 =
            FStar_List.fold_left
              (fun uu____1604  ->
                 fun u1  ->
                   match uu____1604 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1629 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1629 with
                        | (k_u,n1) ->
                            let uu____1644 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1644
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1578 with
          | (uu____1662,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1687 =
                   let uu____1688 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____1688  in
                 match uu____1687 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1706 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1715 ->
                   let uu____1716 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____1716
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1722 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1731 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1740 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1747 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1747 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1764 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1764 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1772 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1780 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1780 with
                                  | (uu____1785,m) -> n1 <= m))
                           in
                        if uu____1772 then rest1 else us1
                    | uu____1790 -> us1)
               | uu____1795 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1799 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1799
           in
        let uu____1802 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____1802
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1804 = aux u  in
           match uu____1804 with
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
          (fun uu____1908  ->
             let uu____1909 = FStar_Syntax_Print.tag_of_term t  in
             let uu____1910 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1909
               uu____1910);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1917 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1919 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1944 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1945 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1946 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1947 ->
                  let uu____1964 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars)
                     in
                  if uu____1964
                  then
                    let uu____1965 =
                      let uu____1966 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____1967 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1966 uu____1967
                       in
                    failwith uu____1965
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1970 =
                    let uu____1971 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____1971  in
                  mk uu____1970 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1978 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1978
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1980 = lookup_bvar env x  in
                  (match uu____1980 with
                   | Univ uu____1983 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1986,uu____1987) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2099 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2099 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____2127 =
                         let uu____2128 =
                           let uu____2145 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____2145)  in
                         FStar_Syntax_Syntax.Tm_abs uu____2128  in
                       mk uu____2127 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2176 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2176 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2218 =
                    let uu____2229 =
                      let uu____2236 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____2236]  in
                    closures_as_binders_delayed cfg env uu____2229  in
                  (match uu____2218 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____2254 =
                         let uu____2255 =
                           let uu____2262 =
                             let uu____2263 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____2263
                               FStar_Pervasives_Native.fst
                              in
                           (uu____2262, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____2255  in
                       mk uu____2254 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2354 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____2354
                    | FStar_Util.Inr c ->
                        let uu____2368 = close_comp cfg env c  in
                        FStar_Util.Inr uu____2368
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____2384 =
                    let uu____2385 =
                      let uu____2412 = closure_as_term_delayed cfg env t11
                         in
                      (uu____2412, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2385  in
                  mk uu____2384 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2463 =
                    let uu____2464 =
                      let uu____2471 = closure_as_term_delayed cfg env t'  in
                      let uu____2474 =
                        let uu____2475 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____2475  in
                      (uu____2471, uu____2474)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2464  in
                  mk uu____2463 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2535 =
                    let uu____2536 =
                      let uu____2543 = closure_as_term_delayed cfg env t'  in
                      let uu____2546 =
                        let uu____2547 =
                          let uu____2554 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____2554)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____2547  in
                      (uu____2543, uu____2546)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2536  in
                  mk uu____2535 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2573 =
                    let uu____2574 =
                      let uu____2581 = closure_as_term_delayed cfg env t'  in
                      let uu____2584 =
                        let uu____2585 =
                          let uu____2594 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____2594)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2585  in
                      (uu____2581, uu____2584)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2574  in
                  mk uu____2573 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2607 =
                    let uu____2608 =
                      let uu____2615 = closure_as_term_delayed cfg env t'  in
                      (uu____2615, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2608  in
                  mk uu____2607 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2655  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____2674 =
                    let uu____2685 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____2685
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____2704 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___93_2716 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_2716.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_2716.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2704))
                     in
                  (match uu____2674 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___94_2732 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_2732.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_2732.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2743,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2802  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____2827 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____2827
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2847  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____2869 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____2869
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___95_2881 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___95_2881.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___95_2881.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___96_2882 = lb  in
                    let uu____2883 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___96_2882.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___96_2882.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2883
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2913  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____3002 =
                    match uu____3002 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3057 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3078 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3138  ->
                                        fun uu____3139  ->
                                          match (uu____3138, uu____3139) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3230 =
                                                norm_pat env3 p1  in
                                              (match uu____3230 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____3078 with
                               | (pats1,env3) ->
                                   ((let uu___97_3312 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___97_3312.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___98_3331 = x  in
                                let uu____3332 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___98_3331.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_3331.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3332
                                }  in
                              ((let uu___99_3346 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___99_3346.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___100_3357 = x  in
                                let uu____3358 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___100_3357.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___100_3357.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3358
                                }  in
                              ((let uu___101_3372 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___101_3372.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___102_3388 = x  in
                                let uu____3389 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3388.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3388.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3389
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___103_3396 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3396.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____3399 = norm_pat env1 pat  in
                        (match uu____3399 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3428 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____3428
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____3434 =
                    let uu____3435 =
                      let uu____3458 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____3458)  in
                    FStar_Syntax_Syntax.Tm_match uu____3435  in
                  mk uu____3434 t1.FStar_Syntax_Syntax.pos))

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
        | uu____3544 -> closure_as_term cfg env t

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
        | uu____3570 ->
            FStar_List.map
              (fun uu____3587  ->
                 match uu____3587 with
                 | (x,imp) ->
                     let uu____3606 = closure_as_term_delayed cfg env x  in
                     (uu____3606, imp)) args

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
        let uu____3620 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3669  ->
                  fun uu____3670  ->
                    match (uu____3669, uu____3670) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___104_3740 = b  in
                          let uu____3741 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___104_3740.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___104_3740.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3741
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____3620 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____3834 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3847 = closure_as_term_delayed cfg env t  in
                 let uu____3848 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____3847 uu____3848
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3861 = closure_as_term_delayed cfg env t  in
                 let uu____3862 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3861 uu____3862
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
                        (fun uu___75_3888  ->
                           match uu___75_3888 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3892 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____3892
                           | f -> f))
                    in
                 let uu____3896 =
                   let uu___105_3897 = c1  in
                   let uu____3898 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3898;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___105_3897.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____3896)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___76_3908  ->
            match uu___76_3908 with
            | FStar_Syntax_Syntax.DECREASES uu____3909 -> false
            | uu____3912 -> true))

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
                   (fun uu___77_3930  ->
                      match uu___77_3930 with
                      | FStar_Syntax_Syntax.DECREASES uu____3931 -> false
                      | uu____3934 -> true))
               in
            let rc1 =
              let uu___106_3936 = rc  in
              let uu____3937 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___106_3936.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3937;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____3944 -> lopt

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
  let arg_as_list a u a =
    let uu____4029 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4029  in
  let arg_as_bounded_int uu____4057 =
    match uu____4057 with
    | (a,uu____4069) ->
        let uu____4076 =
          let uu____4077 = FStar_Syntax_Subst.compress a  in
          uu____4077.FStar_Syntax_Syntax.n  in
        (match uu____4076 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4087;
                FStar_Syntax_Syntax.vars = uu____4088;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4090;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4091;_},uu____4092)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4131 =
               let uu____4136 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____4136)  in
             FStar_Pervasives_Native.Some uu____4131
         | uu____4141 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4181 = f a  in FStar_Pervasives_Native.Some uu____4181
    | uu____4182 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4230 = f a0 a1  in FStar_Pervasives_Native.Some uu____4230
    | uu____4231 -> FStar_Pervasives_Native.None  in
  let unary_op a413 a414 a415 a416 a417 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4273 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a412  -> (Obj.magic (f res.psc_range)) a412)
                    uu____4273)) a413 a414 a415 a416 a417
     in
  let binary_op a420 a421 a422 a423 a424 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4322 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a418  ->
                       fun a419  -> (Obj.magic (f res.psc_range)) a418 a419)
                    uu____4322)) a420 a421 a422 a423 a424
     in
  let as_primitive_step uu____4346 =
    match uu____4346 with
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
    unary_op () (fun a425  -> (Obj.magic arg_as_int) a425)
      (fun a426  ->
         fun a427  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4394 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____4394)) a426 a427)
     in
  let binary_int_op f =
    binary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           fun a431  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4422 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____4422)) a429
               a430 a431)
     in
  let unary_bool_op f =
    unary_op () (fun a432  -> (Obj.magic arg_as_bool) a432)
      (fun a433  ->
         fun a434  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4443 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____4443)) a433
             a434)
     in
  let binary_bool_op f =
    binary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           fun a438  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4471 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____4471)) a436
               a437 a438)
     in
  let binary_string_op f =
    binary_op () (fun a439  -> (Obj.magic arg_as_string) a439)
      (fun a440  ->
         fun a441  ->
           fun a442  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4499 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____4499))
               a440 a441 a442)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4607 =
          let uu____4616 = as_a a  in
          let uu____4619 = as_b b  in (uu____4616, uu____4619)  in
        (match uu____4607 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4634 =
               let uu____4635 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____4635  in
             FStar_Pervasives_Native.Some uu____4634
         | uu____4636 -> FStar_Pervasives_Native.None)
    | uu____4645 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____4659 =
        let uu____4660 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____4660  in
      mk uu____4659 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____4670 =
      let uu____4673 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____4673  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4670  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____4705 =
      let uu____4706 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____4706  in
    FStar_Syntax_Embeddings.embed_int rng uu____4705  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4724 = arg_as_string a1  in
        (match uu____4724 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4730 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____4730 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4743 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____4743
              | uu____4744 -> FStar_Pervasives_Native.None)
         | uu____4749 -> FStar_Pervasives_Native.None)
    | uu____4752 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____4762 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____4762  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____4786 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4797 =
          let uu____4818 = arg_as_string fn  in
          let uu____4821 = arg_as_int from_line  in
          let uu____4824 = arg_as_int from_col  in
          let uu____4827 = arg_as_int to_line  in
          let uu____4830 = arg_as_int to_col  in
          (uu____4818, uu____4821, uu____4824, uu____4827, uu____4830)  in
        (match uu____4797 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4861 =
                 let uu____4862 = FStar_BigInt.to_int_fs from_l  in
                 let uu____4863 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____4862 uu____4863  in
               let uu____4864 =
                 let uu____4865 = FStar_BigInt.to_int_fs to_l  in
                 let uu____4866 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____4865 uu____4866  in
               FStar_Range.mk_range fn1 uu____4861 uu____4864  in
             let uu____4867 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____4867
         | uu____4872 -> FStar_Pervasives_Native.None)
    | uu____4893 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____4920)::(a1,uu____4922)::(a2,uu____4924)::[] ->
        let uu____4961 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____4961 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4974 -> FStar_Pervasives_Native.None)
    | uu____4975 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____5002)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5011 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____5035 =
      let uu____5050 =
        let uu____5065 =
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
                                                let uu____5363 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____5363,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a443  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a443)
                                                     (fun a444  ->
                                                        fun a445  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a444 a445)))
                                                 in
                                              let uu____5370 =
                                                let uu____5385 =
                                                  let uu____5398 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____5398,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a446  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a446)
                                                       (fun a447  ->
                                                          fun a448  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a447 a448)))
                                                   in
                                                let uu____5405 =
                                                  let uu____5420 =
                                                    let uu____5435 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____5435,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____5444 =
                                                    let uu____5461 =
                                                      let uu____5476 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____5476,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____5485 =
                                                      let uu____5502 =
                                                        let uu____5521 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____5521,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____5502]  in
                                                    uu____5461 :: uu____5485
                                                     in
                                                  uu____5420 :: uu____5444
                                                   in
                                                uu____5385 :: uu____5405  in
                                              uu____5350 :: uu____5370  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5335
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5320
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a449  ->
                                                (Obj.magic arg_as_string)
                                                  a449)
                                             (fun a450  ->
                                                fun a451  ->
                                                  fun a452  ->
                                                    (Obj.magic
                                                       string_compare') a450
                                                      a451 a452)))
                                          :: uu____5305
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a453  ->
                                              (Obj.magic arg_as_bool) a453)
                                           (fun a454  ->
                                              fun a455  ->
                                                (Obj.magic string_of_bool1)
                                                  a454 a455)))
                                        :: uu____5290
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a456  ->
                                            (Obj.magic arg_as_int) a456)
                                         (fun a457  ->
                                            fun a458  ->
                                              (Obj.magic string_of_int1) a457
                                                a458)))
                                      :: uu____5275
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a459  ->
                                          (Obj.magic arg_as_int) a459)
                                       (fun a460  ->
                                          (Obj.magic arg_as_char) a460)
                                       (fun a461  ->
                                          fun a462  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a461 a462)
                                       (fun a463  ->
                                          fun a464  ->
                                            fun a465  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____5738 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____5738 y)) a463
                                                a464 a465)))
                                    :: uu____5260
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5245
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5230
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5215
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5200
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5185
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5170
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a466  -> (Obj.magic arg_as_int) a466)
                         (fun a467  ->
                            fun a468  ->
                              fun a469  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____5905 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5905)) a467 a468 a469)))
                      :: uu____5155
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a470  -> (Obj.magic arg_as_int) a470)
                       (fun a471  ->
                          fun a472  ->
                            fun a473  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5931 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5931)) a471 a472 a473)))
                    :: uu____5140
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a474  -> (Obj.magic arg_as_int) a474)
                     (fun a475  ->
                        fun a476  ->
                          fun a477  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5957 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5957)) a475 a476 a477)))
                  :: uu____5125
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a478  -> (Obj.magic arg_as_int) a478)
                   (fun a479  ->
                      fun a480  ->
                        fun a481  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____5983 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____5983)) a479 a480 a481)))
                :: uu____5110
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5095
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5080
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5065
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5050
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5035
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
      let uu____6133 =
        let uu____6134 =
          let uu____6135 = FStar_Syntax_Syntax.as_arg c  in [uu____6135]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6134  in
      uu____6133 FStar_Pervasives_Native.None r  in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6170 =
              let uu____6183 = FStar_Parser_Const.p2l ["FStar"; m; "add"]  in
              (uu____6183, (Prims.parse_int "2"),
                (binary_op ()
                   (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                   (fun a483  ->
                      fun a484  ->
                        fun a485  ->
                          (Obj.magic
                             (fun r  ->
                                fun uu____6199  ->
                                  fun uu____6200  ->
                                    match (uu____6199, uu____6200) with
                                    | ((int_to_t1,x),(uu____6219,y)) ->
                                        let uu____6229 =
                                          FStar_BigInt.add_big_int x y  in
                                        int_as_bounded r int_to_t1 uu____6229))
                            a483 a484 a485)))
               in
            let uu____6230 =
              let uu____6245 =
                let uu____6258 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                   in
                (uu____6258, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a486  -> (Obj.magic arg_as_bounded_int) a486)
                     (fun a487  ->
                        fun a488  ->
                          fun a489  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6274  ->
                                    fun uu____6275  ->
                                      match (uu____6274, uu____6275) with
                                      | ((int_to_t1,x),(uu____6294,y)) ->
                                          let uu____6304 =
                                            FStar_BigInt.sub_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____6304)) a487 a488 a489)))
                 in
              let uu____6305 =
                let uu____6320 =
                  let uu____6333 = FStar_Parser_Const.p2l ["FStar"; m; "mul"]
                     in
                  (uu____6333, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a490  -> (Obj.magic arg_as_bounded_int) a490)
                       (fun a491  ->
                          fun a492  ->
                            fun a493  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6349  ->
                                      fun uu____6350  ->
                                        match (uu____6349, uu____6350) with
                                        | ((int_to_t1,x),(uu____6369,y)) ->
                                            let uu____6379 =
                                              FStar_BigInt.mult_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____6379)) a491 a492 a493)))
                   in
                [uu____6320]  in
              uu____6245 :: uu____6305  in
            uu____6170 :: uu____6230))
     in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
  
let (equality_ops : primitive_step Prims.list) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____6469)::(a1,uu____6471)::(a2,uu____6473)::[] ->
        let uu____6510 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6510 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6516 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6516.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6516.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6520 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6520.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6520.FStar_Syntax_Syntax.vars)
                })
         | uu____6521 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6523)::uu____6524::(a1,uu____6526)::(a2,uu____6528)::[] ->
        let uu____6577 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6577 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6583 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6583.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6583.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6587 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6587.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6587.FStar_Syntax_Syntax.vars)
                })
         | uu____6588 -> FStar_Pervasives_Native.None)
    | uu____6589 -> failwith "Unexpected number of arguments"  in
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
      let uu____6608 =
        let uu____6609 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____6609 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____6608
    with | uu____6615 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____6619 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6619) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6679  ->
           fun subst1  ->
             match uu____6679 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6720,uu____6721)) ->
                      let uu____6780 = b  in
                      (match uu____6780 with
                       | (bv,uu____6788) ->
                           let uu____6789 =
                             let uu____6790 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____6790  in
                           if uu____6789
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____6795 = unembed_binder term1  in
                              match uu____6795 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6802 =
                                      let uu___111_6803 = bv  in
                                      let uu____6804 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_6803.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_6803.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6804
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____6802
                                     in
                                  let b_for_x =
                                    let uu____6808 =
                                      let uu____6815 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6815)
                                       in
                                    FStar_Syntax_Syntax.NT uu____6808  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_6824  ->
                                         match uu___78_6824 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6825,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6827;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6828;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6833 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____6834 -> subst1)) env []
  
let reduce_primops :
  'Auu____6851 'Auu____6852 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6852) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6851 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6893 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps)
             in
          if uu____6893
          then tm
          else
            (let uu____6895 = FStar_Syntax_Util.head_and_args tm  in
             match uu____6895 with
             | (head1,args) ->
                 let uu____6932 =
                   let uu____6933 = FStar_Syntax_Util.un_uinst head1  in
                   uu____6933.FStar_Syntax_Syntax.n  in
                 (match uu____6932 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6937 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps
                         in
                      (match uu____6937 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6954  ->
                                   let uu____6955 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____6956 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____6963 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6955 uu____6956 uu____6963);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6968  ->
                                   let uu____6969 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6969);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6972  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____6974 =
                                 prim_step.interpretation psc args  in
                               match uu____6974 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6980  ->
                                         let uu____6981 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6981);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6987  ->
                                         let uu____6988 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____6989 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6988 uu____6989);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6990 ->
                           (log_primops cfg
                              (fun uu____6994  ->
                                 let uu____6995 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6995);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6999  ->
                            let uu____7000 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7000);
                       (match args with
                        | (a1,uu____7002)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7019 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7031  ->
                            let uu____7032 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7032);
                       (match args with
                        | (t,uu____7034)::(r,uu____7036)::[] ->
                            let uu____7063 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____7063 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7067 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7067.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7067.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7070 -> tm))
                  | uu____7079 -> tm))
  
let reduce_equality :
  'Auu____7084 'Auu____7085 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7085) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7084 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___113_7123 = cfg  in
         {
           steps = [Primops];
           tcenv = (uu___113_7123.tcenv);
           delta_level = (uu___113_7123.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7123.strong);
           memoize_lazy = (uu___113_7123.memoize_lazy);
           normalize_pure_lets = (uu___113_7123.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____7130 'Auu____7131 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7131) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7130 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____7173 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps)
             in
          if uu____7173
          then tm1
          else
            (let w t =
               let uu___114_7185 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7185.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7185.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7201;
                      FStar_Syntax_Syntax.vars = uu____7202;_},uu____7203)
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
                      FStar_Syntax_Syntax.pos = uu____7210;
                      FStar_Syntax_Syntax.vars = uu____7211;_},uu____7212)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7218 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____7223 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____7223
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7244 =
                 match uu____7244 with
                 | (t1,q) ->
                     let uu____7257 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____7257 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7285 -> (t1, q))
                  in
               let uu____7294 = FStar_Syntax_Util.head_and_args t  in
               match uu____7294 with
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
                         FStar_Syntax_Syntax.pos = uu____7391;
                         FStar_Syntax_Syntax.vars = uu____7392;_},uu____7393);
                    FStar_Syntax_Syntax.pos = uu____7394;
                    FStar_Syntax_Syntax.vars = uu____7395;_},args)
                 ->
                 let uu____7421 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____7421
                 then
                   let uu____7422 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____7422 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7477)::
                        (uu____7478,(arg,uu____7480))::[] ->
                        maybe_auto_squash arg
                    | (uu____7545,(arg,uu____7547))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7548)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7613)::uu____7614::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7677::(FStar_Pervasives_Native.Some (false
                                   ),uu____7678)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7741 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7757 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____7757
                    then
                      let uu____7758 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____7758 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7813)::uu____7814::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7877::(FStar_Pervasives_Native.Some (true
                                     ),uu____7878)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7941)::
                          (uu____7942,(arg,uu____7944))::[] ->
                          maybe_auto_squash arg
                      | (uu____8009,(arg,uu____8011))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8012)::[]
                          -> maybe_auto_squash arg
                      | uu____8077 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8093 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____8093
                       then
                         let uu____8094 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____8094 with
                         | uu____8149::(FStar_Pervasives_Native.Some (true
                                        ),uu____8150)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8213)::uu____8214::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8277)::
                             (uu____8278,(arg,uu____8280))::[] ->
                             maybe_auto_squash arg
                         | (uu____8345,(p,uu____8347))::(uu____8348,(q,uu____8350))::[]
                             ->
                             let uu____8415 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____8415
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8417 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8433 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____8433
                          then
                            let uu____8434 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____8434 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8489)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8528)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8567 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8583 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____8583
                             then
                               match args with
                               | (t,uu____8585)::[] ->
                                   let uu____8602 =
                                     let uu____8603 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____8603.FStar_Syntax_Syntax.n  in
                                   (match uu____8602 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8606::[],body,uu____8608) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8635 -> tm1)
                                    | uu____8638 -> tm1)
                               | (uu____8639,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8640))::
                                   (t,uu____8642)::[] ->
                                   let uu____8681 =
                                     let uu____8682 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____8682.FStar_Syntax_Syntax.n  in
                                   (match uu____8681 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8685::[],body,uu____8687) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8714 -> tm1)
                                    | uu____8717 -> tm1)
                               | uu____8718 -> tm1
                             else
                               (let uu____8728 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____8728
                                then
                                  match args with
                                  | (t,uu____8730)::[] ->
                                      let uu____8747 =
                                        let uu____8748 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____8748.FStar_Syntax_Syntax.n  in
                                      (match uu____8747 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8751::[],body,uu____8753)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8780 -> tm1)
                                       | uu____8783 -> tm1)
                                  | (uu____8784,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8785))::(t,uu____8787)::[] ->
                                      let uu____8826 =
                                        let uu____8827 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____8827.FStar_Syntax_Syntax.n  in
                                      (match uu____8826 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8830::[],body,uu____8832)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8859 -> tm1)
                                       | uu____8862 -> tm1)
                                  | uu____8863 -> tm1
                                else
                                  (let uu____8873 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____8873
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8874;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8875;_},uu____8876)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8893;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8894;_},uu____8895)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8912 -> tm1
                                   else
                                     (let uu____8922 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____8922 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8942 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8952;
                    FStar_Syntax_Syntax.vars = uu____8953;_},args)
                 ->
                 let uu____8975 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8975
                 then
                   let uu____8976 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8976 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9031)::
                        (uu____9032,(arg,uu____9034))::[] ->
                        maybe_auto_squash arg
                    | (uu____9099,(arg,uu____9101))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9102)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9167)::uu____9168::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9231::(FStar_Pervasives_Native.Some (false
                                   ),uu____9232)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9295 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9311 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9311
                    then
                      let uu____9312 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9312 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9367)::uu____9368::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9431::(FStar_Pervasives_Native.Some (true
                                     ),uu____9432)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9495)::
                          (uu____9496,(arg,uu____9498))::[] ->
                          maybe_auto_squash arg
                      | (uu____9563,(arg,uu____9565))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9566)::[]
                          -> maybe_auto_squash arg
                      | uu____9631 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9647 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9647
                       then
                         let uu____9648 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9648 with
                         | uu____9703::(FStar_Pervasives_Native.Some (true
                                        ),uu____9704)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9767)::uu____9768::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9831)::
                             (uu____9832,(arg,uu____9834))::[] ->
                             maybe_auto_squash arg
                         | (uu____9899,(p,uu____9901))::(uu____9902,(q,uu____9904))::[]
                             ->
                             let uu____9969 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9969
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9971 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9987 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____9987
                          then
                            let uu____9988 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9988 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10043)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10082)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10121 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10137 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____10137
                             then
                               match args with
                               | (t,uu____10139)::[] ->
                                   let uu____10156 =
                                     let uu____10157 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10157.FStar_Syntax_Syntax.n  in
                                   (match uu____10156 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10160::[],body,uu____10162) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10189 -> tm1)
                                    | uu____10192 -> tm1)
                               | (uu____10193,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10194))::
                                   (t,uu____10196)::[] ->
                                   let uu____10235 =
                                     let uu____10236 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10236.FStar_Syntax_Syntax.n  in
                                   (match uu____10235 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10239::[],body,uu____10241) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10268 -> tm1)
                                    | uu____10271 -> tm1)
                               | uu____10272 -> tm1
                             else
                               (let uu____10282 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10282
                                then
                                  match args with
                                  | (t,uu____10284)::[] ->
                                      let uu____10301 =
                                        let uu____10302 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10302.FStar_Syntax_Syntax.n  in
                                      (match uu____10301 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10305::[],body,uu____10307)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10334 -> tm1)
                                       | uu____10337 -> tm1)
                                  | (uu____10338,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10339))::(t,uu____10341)::[] ->
                                      let uu____10380 =
                                        let uu____10381 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10381.FStar_Syntax_Syntax.n  in
                                      (match uu____10380 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10384::[],body,uu____10386)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10413 -> tm1)
                                       | uu____10416 -> tm1)
                                  | uu____10417 -> tm1
                                else
                                  (let uu____10427 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10427
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10428;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10429;_},uu____10430)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10447;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10448;_},uu____10449)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10466 -> tm1
                                   else
                                     (let uu____10476 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10476 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10496 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____10511 -> tm1)
  
let maybe_simplify :
  'Auu____10518 'Auu____10519 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10519) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10518 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          (let uu____10562 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380")
              in
           if uu____10562
           then
             let uu____10563 = FStar_Syntax_Print.term_to_string tm  in
             let uu____10564 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10563 uu____10564
           else ());
          tm'
  
let is_norm_request :
  'Auu____10570 .
    FStar_Syntax_Syntax.term -> 'Auu____10570 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10583 =
        let uu____10590 =
          let uu____10591 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10591.FStar_Syntax_Syntax.n  in
        (uu____10590, args)  in
      match uu____10583 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10597::uu____10598::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10602::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10607::uu____10608::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10611 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___79_10622  ->
    match uu___79_10622 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10628 =
          let uu____10631 =
            let uu____10632 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10632  in
          [uu____10631]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10628
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10647 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10647) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10685 =
          let uu____10688 =
            let uu____10693 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step
               in
            uu____10693 s  in
          FStar_All.pipe_right uu____10688 FStar_Util.must  in
        FStar_All.pipe_right uu____10685 tr_norm_steps  in
      match args with
      | uu____10718::(tm,uu____10720)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____10743)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____10758)::uu____10759::(tm,uu____10761)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
            let uu____10801 =
              let uu____10804 = full_norm steps  in parse_steps uu____10804
               in
            Beta :: uu____10801  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____10813 -> failwith "Impossible"
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___80_10830  ->
    match uu___80_10830 with
    | (App
        (uu____10833,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10834;
                       FStar_Syntax_Syntax.vars = uu____10835;_},uu____10836,uu____10837))::uu____10838
        -> true
    | uu____10845 -> false
  
let firstn :
  'Auu____10851 .
    Prims.int ->
      'Auu____10851 Prims.list ->
        ('Auu____10851 Prims.list,'Auu____10851 Prims.list)
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
          (uu____10887,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10888;
                         FStar_Syntax_Syntax.vars = uu____10889;_},uu____10890,uu____10891))::uu____10892
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10899 -> false
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11046  ->
               let uu____11047 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11048 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11049 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11056 =
                 let uu____11057 =
                   let uu____11060 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11060
                    in
                 stack_to_string uu____11057  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11047 uu____11048 uu____11049 uu____11056);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11083 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11108 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11125 =
                 let uu____11126 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos  in
                 let uu____11127 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11126 uu____11127
                  in
               failwith uu____11125
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11128 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11145 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11146 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11147;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11148;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11151;
                 FStar_Syntax_Syntax.fv_delta = uu____11152;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11153;
                 FStar_Syntax_Syntax.fv_delta = uu____11154;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11155);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11163 = FStar_Syntax_Syntax.lid_of_fv fv  in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11163 ->
               let b = should_reify cfg stack  in
               (log cfg
                  (fun uu____11169  ->
                     let uu____11170 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____11171 = FStar_Util.string_of_bool b  in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11170 uu____11171);
                if b
                then
                  (let uu____11172 = FStar_List.tl stack  in
                   do_unfold_fv cfg env uu____11172 t1 fv)
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
                 let uu___115_11211 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11211.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11211.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11244 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____11244) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11252 = cfg  in
                 let uu____11253 =
                   FStar_List.filter
                     (fun uu___81_11256  ->
                        match uu___81_11256 with
                        | UnfoldOnly uu____11257 -> false
                        | NoDeltaSteps  -> false
                        | uu____11260 -> true) cfg.steps
                    in
                 {
                   steps = uu____11253;
                   tcenv = (uu___116_11252.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11252.primitive_steps);
                   strong = (uu___116_11252.strong);
                   memoize_lazy = (uu___116_11252.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11261 = get_norm_request (norm cfg' env []) args  in
               (match uu____11261 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11277 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11282  ->
                                match uu___82_11282 with
                                | UnfoldUntil uu____11283 -> true
                                | UnfoldOnly uu____11284 -> true
                                | uu____11287 -> false))
                         in
                      if uu____11277
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___117_11292 = cfg  in
                      {
                        steps = s;
                        tcenv = (uu___117_11292.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11292.primitive_steps);
                        strong = (uu___117_11292.strong);
                        memoize_lazy = (uu___117_11292.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      let uu____11299 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms")
                         in
                      if uu____11299
                      then
                        let uu____11302 =
                          let uu____11303 =
                            let uu____11308 = FStar_Util.now ()  in
                            (t1, uu____11308)  in
                          Debug uu____11303  in
                        uu____11302 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11312 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11312
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11319 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____11319
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11322 =
                      let uu____11329 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11329, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11322  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11342  ->
                         match uu___83_11342 with
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
                 let uu____11345 =
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
                 if uu____11345
                 then false
                 else
                   (let uu____11347 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11354  ->
                              match uu___84_11354 with
                              | UnfoldOnly uu____11355 -> true
                              | uu____11358 -> false))
                       in
                    match uu____11347 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11362 -> should_delta)
                  in
               (log cfg
                  (fun uu____11370  ->
                     let uu____11371 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____11372 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos
                        in
                     let uu____11373 =
                       FStar_Util.string_of_bool should_delta1  in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11371 uu____11372 uu____11373);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11376 = lookup_bvar env x  in
               (match uu____11376 with
                | Univ uu____11379 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11428 = FStar_ST.op_Bang r  in
                      (match uu____11428 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11546  ->
                                 let uu____11547 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____11548 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11547
                                   uu____11548);
                            (let uu____11549 =
                               let uu____11550 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____11550.FStar_Syntax_Syntax.n  in
                             match uu____11549 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11553 ->
                                 norm cfg env2 stack t'
                             | uu____11570 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11640)::uu____11641 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11650)::uu____11651 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11661,uu____11662))::stack_rest ->
                    (match c with
                     | Univ uu____11666 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11675 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11696  ->
                                    let uu____11697 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11697);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11737  ->
                                    let uu____11738 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11738);
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
                       (fun uu____11816  ->
                          let uu____11817 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11817);
                     norm cfg env stack1 t1)
                | (Debug uu____11818)::uu____11819 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11826 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11826
                    else
                      (let uu____11828 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11828 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11870  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11898 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____11898
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11908 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11908)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_11913 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_11913.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_11913.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11914 -> lopt  in
                           (log cfg
                              (fun uu____11920  ->
                                 let uu____11921 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11921);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_11930 = cfg  in
                               {
                                 steps = (uu___119_11930.steps);
                                 tcenv = (uu___119_11930.tcenv);
                                 delta_level = (uu___119_11930.delta_level);
                                 primitive_steps =
                                   (uu___119_11930.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_11930.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_11930.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11941)::uu____11942 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11949 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11949
                    else
                      (let uu____11951 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11951 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11993  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12021 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12021
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12031 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12031)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12036 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12036.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12036.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12037 -> lopt  in
                           (log cfg
                              (fun uu____12043  ->
                                 let uu____12044 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12044);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12053 = cfg  in
                               {
                                 steps = (uu___119_12053.steps);
                                 tcenv = (uu___119_12053.tcenv);
                                 delta_level = (uu___119_12053.delta_level);
                                 primitive_steps =
                                   (uu___119_12053.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12053.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12053.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12064)::uu____12065 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12076 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12076
                    else
                      (let uu____12078 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12078 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12120  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12148 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12148
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12158 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12158)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12163 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12163.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12163.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12164 -> lopt  in
                           (log cfg
                              (fun uu____12170  ->
                                 let uu____12171 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12171);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12180 = cfg  in
                               {
                                 steps = (uu___119_12180.steps);
                                 tcenv = (uu___119_12180.tcenv);
                                 delta_level = (uu___119_12180.delta_level);
                                 primitive_steps =
                                   (uu___119_12180.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12180.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12180.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12191)::uu____12192 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12203 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12203
                    else
                      (let uu____12205 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12205 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12247  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12275 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12275
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12285 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12285)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12290 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12290.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12290.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12291 -> lopt  in
                           (log cfg
                              (fun uu____12297  ->
                                 let uu____12298 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12298);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12307 = cfg  in
                               {
                                 steps = (uu___119_12307.steps);
                                 tcenv = (uu___119_12307.tcenv);
                                 delta_level = (uu___119_12307.delta_level);
                                 primitive_steps =
                                   (uu___119_12307.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12307.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12307.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12318)::uu____12319 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12334 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12334
                    else
                      (let uu____12336 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12336 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12378  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12406 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12406
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12416 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12416)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12421 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12421.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12421.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12422 -> lopt  in
                           (log cfg
                              (fun uu____12428  ->
                                 let uu____12429 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12429);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12438 = cfg  in
                               {
                                 steps = (uu___119_12438.steps);
                                 tcenv = (uu___119_12438.tcenv);
                                 delta_level = (uu___119_12438.delta_level);
                                 primitive_steps =
                                   (uu___119_12438.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12438.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12438.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12449 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12449
                    else
                      (let uu____12451 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12451 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12493  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12521 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12521
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12531 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12531)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12536 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12536.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12536.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12537 -> lopt  in
                           (log cfg
                              (fun uu____12543  ->
                                 let uu____12544 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12544);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___119_12553 = cfg  in
                               {
                                 steps = (uu___119_12553.steps);
                                 tcenv = (uu___119_12553.tcenv);
                                 delta_level = (uu___119_12553.delta_level);
                                 primitive_steps =
                                   (uu___119_12553.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12553.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12553.normalize_pure_lets)
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
                      (fun uu____12602  ->
                         fun stack1  ->
                           match uu____12602 with
                           | (a,aq) ->
                               let uu____12614 =
                                 let uu____12615 =
                                   let uu____12622 =
                                     let uu____12623 =
                                       let uu____12654 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12654, false)  in
                                     Clos uu____12623  in
                                   (uu____12622, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12615  in
                               uu____12614 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12738  ->
                     let uu____12739 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12739);
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
                             ((let uu___120_12775 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_12775.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_12775.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12776 ->
                      let uu____12781 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12781)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12784 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12784 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12815 =
                          let uu____12816 =
                            let uu____12823 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___121_12825 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_12825.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_12825.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12823)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12816  in
                        mk uu____12815 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12844 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12844
               else
                 (let uu____12846 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12846 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12854 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12878  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12854 c1  in
                      let t2 =
                        let uu____12900 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12900 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               FStar_List.contains Unascribe cfg.steps ->
               norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13011)::uu____13012 ->
                    (log cfg
                       (fun uu____13023  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13024)::uu____13025 ->
                    (log cfg
                       (fun uu____13036  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13037,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13038;
                                   FStar_Syntax_Syntax.vars = uu____13039;_},uu____13040,uu____13041))::uu____13042
                    ->
                    (log cfg
                       (fun uu____13051  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13052)::uu____13053 ->
                    (log cfg
                       (fun uu____13064  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13065 ->
                    (log cfg
                       (fun uu____13068  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13072  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13089 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13089
                         | FStar_Util.Inr c ->
                             let uu____13097 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13097
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13110 =
                               let uu____13111 =
                                 let uu____13138 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13138, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13111
                                in
                             mk uu____13110 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____13157 ->
                           let uu____13158 =
                             let uu____13159 =
                               let uu____13160 =
                                 let uu____13187 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13187, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13160
                                in
                             mk uu____13159 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____13158))))
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
                         let uu____13297 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13297 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13317 = cfg  in
                               let uu____13318 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___122_13317.steps);
                                 tcenv = uu____13318;
                                 delta_level = (uu___122_13317.delta_level);
                                 primitive_steps =
                                   (uu___122_13317.primitive_steps);
                                 strong = (uu___122_13317.strong);
                                 memoize_lazy = (uu___122_13317.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___122_13317.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____13323 =
                                 let uu____13324 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13324  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13323
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___123_13327 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13327.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13327.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             }))
                  in
               let uu____13328 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13328
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13339,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13340;
                               FStar_Syntax_Syntax.lbunivs = uu____13341;
                               FStar_Syntax_Syntax.lbtyp = uu____13342;
                               FStar_Syntax_Syntax.lbeff = uu____13343;
                               FStar_Syntax_Syntax.lbdef = uu____13344;_}::uu____13345),uu____13346)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____13382 =
                 (let uu____13385 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____13385) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13387 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)
                             in
                          Prims.op_Negation uu____13387)))
                  in
               if uu____13382
               then
                 let binder =
                   let uu____13389 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13389  in
                 let env1 =
                   let uu____13399 =
                     let uu____13406 =
                       let uu____13407 =
                         let uu____13438 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13438,
                           false)
                          in
                       Clos uu____13407  in
                     ((FStar_Pervasives_Native.Some binder), uu____13406)  in
                   uu____13399 :: env  in
                 (log cfg
                    (fun uu____13531  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if FStar_List.contains Weak cfg.steps
                 then
                   (log cfg
                      (fun uu____13535  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____13536 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____13536))
                 else
                   (let uu____13538 =
                      let uu____13543 =
                        let uu____13544 =
                          let uu____13545 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____13545
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____13544]  in
                      FStar_Syntax_Subst.open_term uu____13543 body  in
                    match uu____13538 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____13554  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____13562 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____13562  in
                            FStar_Util.Inl
                              (let uu___124_13572 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___124_13572.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___124_13572.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____13575  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___125_13577 = lb  in
                             let uu____13578 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___125_13577.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___125_13577.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13578
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13613  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___126_13636 = cfg  in
                             {
                               steps = (uu___126_13636.steps);
                               tcenv = (uu___126_13636.tcenv);
                               delta_level = (uu___126_13636.delta_level);
                               primitive_steps =
                                 (uu___126_13636.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___126_13636.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___126_13636.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____13639  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13656 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13656 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13692 =
                               let uu___127_13693 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13693.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13693.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13692  in
                           let uu____13694 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13694 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13720 =
                                   FStar_List.map (fun uu____13736  -> dummy)
                                     lbs1
                                    in
                                 let uu____13737 =
                                   let uu____13746 =
                                     FStar_List.map
                                       (fun uu____13766  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13746 env  in
                                 FStar_List.append uu____13720 uu____13737
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13790 =
                                       let uu___128_13791 = rc  in
                                       let uu____13792 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_13791.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13792;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_13791.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13790
                                 | uu____13799 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___129_13803 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_13803.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_13803.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
                      let uu____13813 =
                        FStar_List.map (fun uu____13829  -> dummy) lbs2  in
                      FStar_List.append uu____13813 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13837 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13837 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_13853 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_13853.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_13853.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13880 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13880
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13899 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13975  ->
                        match uu____13975 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14096 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14096.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14096.FStar_Syntax_Syntax.sort)
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
               (match uu____13899 with
                | (rec_env,memos,uu____14309) ->
                    let uu____14362 =
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
                             let uu____14673 =
                               let uu____14680 =
                                 let uu____14681 =
                                   let uu____14712 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14712, false)
                                    in
                                 Clos uu____14681  in
                               (FStar_Pervasives_Native.None, uu____14680)
                                in
                             uu____14673 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14822  ->
                     let uu____14823 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14823);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14845 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14847::uu____14848 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14853) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14854 ->
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
                             | uu____14885 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14899 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14899
                              | uu____14910 -> m  in
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
              let uu____14922 = FStar_Syntax_Syntax.range_of_fv f  in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14922  in
            let uu____14923 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            match uu____14923 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14936  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14947  ->
                      let uu____14948 = FStar_Syntax_Print.term_to_string t0
                         in
                      let uu____14949 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14948
                        uu____14949);
                 (let t1 =
                    let uu____14951 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____14953 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac)
                            in
                         Prims.op_Negation uu____14953)
                       in
                    if uu____14951
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
                    | (UnivArgs (us',uu____14963))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env)
                           in
                        norm cfg env1 stack1 t1
                    | uu____15018 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15021 ->
                        let uu____15024 =
                          let uu____15025 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15025
                           in
                        failwith uu____15024
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
                let uu____15046 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations)
                   in
                if uu____15046
                then
                  let uu___132_15047 = cfg  in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_15047.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_15047.primitive_steps);
                    strong = (uu___132_15047.strong);
                    memoize_lazy = (uu___132_15047.memoize_lazy);
                    normalize_pure_lets =
                      (uu___132_15047.normalize_pure_lets)
                  }
                else
                  (let uu___133_15049 = cfg  in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_15049.tcenv);
                     delta_level = (uu___133_15049.delta_level);
                     primitive_steps = (uu___133_15049.primitive_steps);
                     strong = (uu___133_15049.strong);
                     memoize_lazy = (uu___133_15049.memoize_lazy);
                     normalize_pure_lets =
                       (uu___133_15049.normalize_pure_lets)
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
                let head0 = head1  in
                let head2 = FStar_Syntax_Util.unascribe head1  in
                log cfg
                  (fun uu____15079  ->
                     let uu____15080 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____15081 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15080
                       uu____15081);
                (let uu____15082 =
                   let uu____15083 = FStar_Syntax_Subst.compress head2  in
                   uu____15083.FStar_Syntax_Syntax.n  in
                 match uu____15082 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____15101 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15101 with
                      | (uu____15102,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15108 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15116 =
                                   let uu____15117 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____15117.FStar_Syntax_Syntax.n  in
                                 match uu____15116 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15123,uu____15124))
                                     ->
                                     let uu____15133 =
                                       let uu____15134 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____15134.FStar_Syntax_Syntax.n  in
                                     (match uu____15133 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15140,msrc,uu____15142))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15151 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15151
                                      | uu____15152 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15153 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____15154 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____15154 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15159 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15159.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15159.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15159.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      }  in
                                    let uu____15160 = FStar_List.tl stack  in
                                    let uu____15161 =
                                      let uu____15162 =
                                        let uu____15165 =
                                          let uu____15166 =
                                            let uu____15179 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____15179)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15166
                                           in
                                        FStar_Syntax_Syntax.mk uu____15165
                                         in
                                      uu____15162
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____15160 uu____15161
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15195 =
                                      let uu____15196 = is_return body  in
                                      match uu____15196 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15200;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15201;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15206 -> false  in
                                    if uu____15195
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
                                         let uu____15229 =
                                           let uu____15232 =
                                             let uu____15233 =
                                               let uu____15250 =
                                                 let uu____15253 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____15253]  in
                                               (uu____15250, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15233
                                              in
                                           FStar_Syntax_Syntax.mk uu____15232
                                            in
                                         uu____15229
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____15269 =
                                           let uu____15270 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____15270.FStar_Syntax_Syntax.n
                                            in
                                         match uu____15269 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15276::uu____15277::[])
                                             ->
                                             let uu____15284 =
                                               let uu____15287 =
                                                 let uu____15288 =
                                                   let uu____15295 =
                                                     let uu____15298 =
                                                       let uu____15299 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15299
                                                        in
                                                     let uu____15300 =
                                                       let uu____15303 =
                                                         let uu____15304 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15304
                                                          in
                                                       [uu____15303]  in
                                                     uu____15298 ::
                                                       uu____15300
                                                      in
                                                   (bind1, uu____15295)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15288
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15287
                                                in
                                             uu____15284
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15312 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____15318 =
                                           let uu____15321 =
                                             let uu____15322 =
                                               let uu____15337 =
                                                 let uu____15340 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____15341 =
                                                   let uu____15344 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____15345 =
                                                     let uu____15348 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____15349 =
                                                       let uu____15352 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____15353 =
                                                         let uu____15356 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____15357 =
                                                           let uu____15360 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____15360]  in
                                                         uu____15356 ::
                                                           uu____15357
                                                          in
                                                       uu____15352 ::
                                                         uu____15353
                                                        in
                                                     uu____15348 ::
                                                       uu____15349
                                                      in
                                                   uu____15344 :: uu____15345
                                                    in
                                                 uu____15340 :: uu____15341
                                                  in
                                               (bind_inst, uu____15337)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15322
                                              in
                                           FStar_Syntax_Syntax.mk uu____15321
                                            in
                                         uu____15318
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____15372  ->
                                            let uu____15373 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____15374 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____15373 uu____15374);
                                       (let uu____15375 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____15375 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____15399 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15399 with
                      | (uu____15400,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15435 =
                                  let uu____15436 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15436.FStar_Syntax_Syntax.n  in
                                match uu____15435 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15442) -> t2
                                | uu____15447 -> head3  in
                              let uu____15448 =
                                let uu____15449 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15449.FStar_Syntax_Syntax.n  in
                              match uu____15448 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15455 -> FStar_Pervasives_Native.None
                               in
                            let uu____15456 = maybe_extract_fv head3  in
                            match uu____15456 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15466 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15466
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____15471 = maybe_extract_fv head4
                                     in
                                  match uu____15471 with
                                  | FStar_Pervasives_Native.Some uu____15476
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15477 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____15482 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15497 =
                              match uu____15497 with
                              | (e,q) ->
                                  let uu____15504 =
                                    let uu____15505 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15505.FStar_Syntax_Syntax.n  in
                                  (match uu____15504 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15520 -> false)
                               in
                            let uu____15521 =
                              let uu____15522 =
                                let uu____15529 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15529 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15522
                               in
                            if uu____15521
                            then
                              let uu____15534 =
                                let uu____15535 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15535
                                 in
                              failwith uu____15534
                            else ());
                           (let uu____15537 = maybe_unfold_action head_app
                               in
                            match uu____15537 with
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
                                (log cfg
                                   (fun uu____15578  ->
                                      let uu____15579 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____15580 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15579 uu____15580);
                                 (let uu____15581 = FStar_List.tl stack  in
                                  norm cfg env uu____15581 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15583) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15607 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15607  in
                     (log cfg
                        (fun uu____15611  ->
                           let uu____15612 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15612);
                      (let uu____15613 = FStar_List.tl stack  in
                       norm cfg env uu____15613 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15615) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15740  ->
                               match uu____15740 with
                               | (pat,wopt,tm) ->
                                   let uu____15788 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15788)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____15820 = FStar_List.tl stack  in
                     norm cfg env uu____15820 tm
                 | uu____15821 -> fallback ())

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
              (fun uu____15835  ->
                 let uu____15836 = FStar_Ident.string_of_lid msrc  in
                 let uu____15837 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15838 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15836
                   uu____15837 uu____15838);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____15840 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15840 with
               | (uu____15841,return_repr) ->
                   let return_inst =
                     let uu____15850 =
                       let uu____15851 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15851.FStar_Syntax_Syntax.n  in
                     match uu____15850 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15857::[]) ->
                         let uu____15864 =
                           let uu____15867 =
                             let uu____15868 =
                               let uu____15875 =
                                 let uu____15878 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15878]  in
                               (return_tm, uu____15875)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15868  in
                           FStar_Syntax_Syntax.mk uu____15867  in
                         uu____15864 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15886 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15889 =
                     let uu____15892 =
                       let uu____15893 =
                         let uu____15908 =
                           let uu____15911 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15912 =
                             let uu____15915 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15915]  in
                           uu____15911 :: uu____15912  in
                         (return_inst, uu____15908)  in
                       FStar_Syntax_Syntax.Tm_app uu____15893  in
                     FStar_Syntax_Syntax.mk uu____15892  in
                   uu____15889 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15924 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____15924 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15927 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____15927
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15928;
                     FStar_TypeChecker_Env.mtarget = uu____15929;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15930;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____15945 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____15945
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15946;
                     FStar_TypeChecker_Env.mtarget = uu____15947;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15948;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15972 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____15973 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____15972 t FStar_Syntax_Syntax.tun uu____15973)

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
                (fun uu____16029  ->
                   match uu____16029 with
                   | (a,imp) ->
                       let uu____16040 = norm cfg env [] a  in
                       (uu____16040, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_16054 = comp  in
            let uu____16055 =
              let uu____16056 =
                let uu____16065 = norm cfg env [] t  in
                let uu____16066 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____16065, uu____16066)  in
              FStar_Syntax_Syntax.Total uu____16056  in
            {
              FStar_Syntax_Syntax.n = uu____16055;
              FStar_Syntax_Syntax.pos =
                (uu___135_16054.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_16054.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_16081 = comp  in
            let uu____16082 =
              let uu____16083 =
                let uu____16092 = norm cfg env [] t  in
                let uu____16093 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____16092, uu____16093)  in
              FStar_Syntax_Syntax.GTotal uu____16083  in
            {
              FStar_Syntax_Syntax.n = uu____16082;
              FStar_Syntax_Syntax.pos =
                (uu___136_16081.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16081.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16145  ->
                      match uu____16145 with
                      | (a,i) ->
                          let uu____16156 = norm cfg env [] a  in
                          (uu____16156, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16167  ->
                      match uu___85_16167 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16171 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____16171
                      | f -> f))
               in
            let uu___137_16175 = comp  in
            let uu____16176 =
              let uu____16177 =
                let uu___138_16178 = ct  in
                let uu____16179 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____16180 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____16183 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16179;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16178.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16180;
                  FStar_Syntax_Syntax.effect_args = uu____16183;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____16177  in
            {
              FStar_Syntax_Syntax.n = uu____16176;
              FStar_Syntax_Syntax.pos =
                (uu___137_16175.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16175.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____16194  ->
        match uu____16194 with
        | (x,imp) ->
            let uu____16197 =
              let uu___139_16198 = x  in
              let uu____16199 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16198.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16198.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16199
              }  in
            (uu____16197, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16205 =
          FStar_List.fold_left
            (fun uu____16223  ->
               fun b  ->
                 match uu____16223 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16205 with | (nbs,uu____16263) -> FStar_List.rev nbs

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
            let uu____16279 =
              let uu___140_16280 = rc  in
              let uu____16281 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16280.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16281;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16280.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16279
        | uu____16288 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16301  ->
               let uu____16302 = FStar_Syntax_Print.tag_of_term t  in
               let uu____16303 = FStar_Syntax_Print.term_to_string t  in
               let uu____16304 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____16311 =
                 let uu____16312 =
                   let uu____16315 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16315
                    in
                 stack_to_string uu____16312  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16302 uu____16303 uu____16304 uu____16311);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16345 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms")
                    in
                 if uu____16345
                 then
                   let time_now = FStar_Util.now ()  in
                   let uu____16347 =
                     let uu____16348 =
                       let uu____16349 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____16349  in
                     FStar_Util.string_of_int uu____16348  in
                   let uu____16354 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____16355 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16347 uu____16354 uu____16355
                 else ());
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____16409  ->
                     let uu____16410 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16410);
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
               let uu____16446 =
                 let uu___141_16447 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16447.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16447.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____16446
           | (Arg (Univ uu____16448,uu____16449,uu____16450))::uu____16451 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16454,uu____16455))::uu____16456 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____16472),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16525  ->
                     let uu____16526 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16526);
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
                  (let uu____16536 = FStar_ST.op_Bang m  in
                   match uu____16536 with
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
                   | FStar_Pervasives_Native.Some (uu____16673,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____16720 =
                 log cfg
                   (fun uu____16724  ->
                      let uu____16725 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16725);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____16729 =
                 let uu____16730 = FStar_Syntax_Subst.compress t1  in
                 uu____16730.FStar_Syntax_Syntax.n  in
               (match uu____16729 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16757 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____16757  in
                    (log cfg
                       (fun uu____16761  ->
                          let uu____16762 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16762);
                     (let uu____16763 = FStar_List.tl stack  in
                      norm cfg env1 uu____16763 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16764);
                       FStar_Syntax_Syntax.pos = uu____16765;
                       FStar_Syntax_Syntax.vars = uu____16766;_},(e,uu____16768)::[])
                    -> norm cfg env1 stack' e
                | uu____16797 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16817  ->
                     let uu____16818 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16818);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____16823 =
                   log cfg
                     (fun uu____16828  ->
                        let uu____16829 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____16830 =
                          let uu____16831 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16848  ->
                                    match uu____16848 with
                                    | (p,uu____16858,uu____16859) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____16831
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16829 uu____16830);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps)
                       in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_16876  ->
                                match uu___86_16876 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16877 -> false))
                         in
                      let steps' = [Exclude Zeta]  in
                      let uu___142_16881 = cfg  in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_16881.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_16881.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_16881.memoize_lazy);
                        normalize_pure_lets =
                          (uu___142_16881.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16913 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16934 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16994  ->
                                    fun uu____16995  ->
                                      match (uu____16994, uu____16995) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17086 = norm_pat env3 p1
                                             in
                                          (match uu____17086 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____16934 with
                           | (pats1,env3) ->
                               ((let uu___143_17168 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17168.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17187 = x  in
                            let uu____17188 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17187.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17187.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17188
                            }  in
                          ((let uu___145_17202 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17202.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17213 = x  in
                            let uu____17214 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17213.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17213.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17214
                            }  in
                          ((let uu___147_17228 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17228.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___148_17244 = x  in
                            let uu____17245 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17244.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17244.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17245
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___149_17252 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17252.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17262 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17276 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____17276 with
                                  | (p,wopt,e) ->
                                      let uu____17296 = norm_pat env1 p  in
                                      (match uu____17296 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17321 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17321
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____17327 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____17327)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17337) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17342 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17343;
                         FStar_Syntax_Syntax.fv_delta = uu____17344;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17345;
                         FStar_Syntax_Syntax.fv_delta = uu____17346;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17347);_}
                       -> true
                   | uu____17354 -> false  in
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
                   let uu____17499 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____17499 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17586 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17625 ->
                                 let uu____17626 =
                                   let uu____17627 = is_cons head1  in
                                   Prims.op_Negation uu____17627  in
                                 FStar_Util.Inr uu____17626)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17652 =
                              let uu____17653 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____17653.FStar_Syntax_Syntax.n  in
                            (match uu____17652 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17671 ->
                                 let uu____17672 =
                                   let uu____17673 = is_cons head1  in
                                   Prims.op_Negation uu____17673  in
                                 FStar_Util.Inr uu____17672))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____17742)::rest_a,(p1,uu____17745)::rest_p) ->
                       let uu____17789 = matches_pat t2 p1  in
                       (match uu____17789 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17838 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17944 = matches_pat scrutinee1 p1  in
                       (match uu____17944 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17984  ->
                                  let uu____17985 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____17986 =
                                    let uu____17987 =
                                      FStar_List.map
                                        (fun uu____17997  ->
                                           match uu____17997 with
                                           | (uu____18002,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____17987
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17985 uu____17986);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18033  ->
                                       match uu____18033 with
                                       | (bv,t2) ->
                                           let uu____18056 =
                                             let uu____18063 =
                                               let uu____18066 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____18066
                                                in
                                             let uu____18067 =
                                               let uu____18068 =
                                                 let uu____18099 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____18099, false)
                                                  in
                                               Clos uu____18068  in
                                             (uu____18063, uu____18067)  in
                                           uu____18056 :: env2) env1 s
                                 in
                              let uu____18216 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____18216)))
                    in
                 let uu____18217 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota))
                    in
                 if uu____18217
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18238  ->
                match uu___87_18238 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18242 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18248 -> d  in
      let uu____18251 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18253 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations)
              in
           Prims.op_Negation uu____18253)
         in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18251
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
            let uu___150_18278 = config s e  in
            {
              steps = (uu___150_18278.steps);
              tcenv = (uu___150_18278.tcenv);
              delta_level = (uu___150_18278.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18278.strong);
              memoize_lazy = (uu___150_18278.memoize_lazy);
              normalize_pure_lets = (uu___150_18278.normalize_pure_lets)
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
      fun t  -> let uu____18303 = config s e  in norm_comp uu____18303 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____18316 = config [] env  in norm_universe uu____18316 [] u
  
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
        let uu____18334 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____18334  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18341 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18360 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18360.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18360.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____18367 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____18367
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
                  let uu___152_18376 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18376.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18376.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18376.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___153_18378 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18378.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18378.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18378.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18378.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___154_18379 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18379.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18379.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18381 -> c
  
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
        let uu____18393 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____18393  in
      let uu____18400 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____18400
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18404  ->
                 let uu____18405 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____18405)
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
            ((let uu____18422 =
                let uu____18427 =
                  let uu____18428 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18428
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____18427)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18422);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18439 = config [AllowUnboundUniverses] env  in
          norm_comp uu____18439 [] c
        with
        | e ->
            ((let uu____18452 =
                let uu____18457 =
                  let uu____18458 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18458
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____18457)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18452);
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
                   let uu____18495 =
                     let uu____18496 =
                       let uu____18503 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____18503)  in
                     FStar_Syntax_Syntax.Tm_refine uu____18496  in
                   mk uu____18495 t01.FStar_Syntax_Syntax.pos
               | uu____18508 -> t2)
          | uu____18509 -> t2  in
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
        let uu____18549 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____18549 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18578 ->
                 let uu____18585 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____18585 with
                  | (actuals,uu____18595,uu____18596) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18610 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____18610 with
                         | (binders,args) ->
                             let uu____18627 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____18627
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
      | uu____18635 ->
          let uu____18636 = FStar_Syntax_Util.head_and_args t  in
          (match uu____18636 with
           | (head1,args) ->
               let uu____18673 =
                 let uu____18674 = FStar_Syntax_Subst.compress head1  in
                 uu____18674.FStar_Syntax_Syntax.n  in
               (match uu____18673 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18677,thead) ->
                    let uu____18703 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____18703 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18745 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18753 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18753.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18753.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18753.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18753.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18753.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18753.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18753.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18753.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18753.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18753.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18753.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18753.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18753.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18753.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18753.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18753.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18753.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18753.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18753.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18753.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18753.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18753.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18753.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18753.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18753.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18753.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18753.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18753.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18753.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18753.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18753.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____18745 with
                            | (uu____18754,ty,uu____18756) ->
                                eta_expand_with_type env t ty))
                | uu____18757 ->
                    let uu____18758 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18766 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18766.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18766.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18766.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18766.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18766.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18766.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18766.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18766.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18766.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18766.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18766.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18766.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18766.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18766.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18766.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18766.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18766.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18766.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18766.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18766.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18766.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18766.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18766.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18766.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18766.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18766.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18766.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18766.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18766.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18766.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18766.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____18758 with
                     | (uu____18767,ty,uu____18769) ->
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
            | (uu____18843,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____18849,FStar_Util.Inl t) ->
                let uu____18855 =
                  let uu____18858 =
                    let uu____18859 =
                      let uu____18872 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____18872)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____18859  in
                  FStar_Syntax_Syntax.mk uu____18858  in
                uu____18855 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____18876 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____18876 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let uu____18903 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____18958 ->
                    let uu____18959 =
                      let uu____18968 =
                        let uu____18969 = FStar_Syntax_Subst.compress t3  in
                        uu____18969.FStar_Syntax_Syntax.n  in
                      (uu____18968, tc)  in
                    (match uu____18959 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____18994) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19031) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19070,FStar_Util.Inl uu____19071) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19094 -> failwith "Impossible")
                 in
              (match uu____18903 with
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
          let uu____19199 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____19199 with
          | (univ_names1,binders1,tc) ->
              let uu____19257 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____19257)
  
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
          let uu____19292 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____19292 with
          | (univ_names1,binders1,tc) ->
              let uu____19352 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____19352)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19385 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____19385 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19413 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19413.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19413.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19413.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19413.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19434 = s  in
          let uu____19435 =
            let uu____19436 =
              let uu____19445 = FStar_List.map (elim_uvars env) sigs  in
              (uu____19445, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____19436  in
          {
            FStar_Syntax_Syntax.sigel = uu____19435;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19434.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19434.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19434.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19434.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19462 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____19462 with
           | (univ_names1,uu____19480,typ1) ->
               let uu___163_19494 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19494.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19494.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19494.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19494.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19500 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____19500 with
           | (univ_names1,uu____19518,typ1) ->
               let uu___164_19532 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19532.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19532.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19532.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19532.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19566 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____19566 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19589 =
                            let uu____19590 =
                              FStar_Syntax_Subst.subst opening t  in
                            remove_uvar_solutions env uu____19590  in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19589
                           in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___165_19593 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19593.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19593.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        }))
             in
          let uu___166_19594 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19594.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19594.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19594.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19594.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19606 = s  in
          let uu____19607 =
            let uu____19608 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____19608  in
          {
            FStar_Syntax_Syntax.sigel = uu____19607;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19606.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19606.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19606.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19606.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19612 = elim_uvars_aux_t env us [] t  in
          (match uu____19612 with
           | (us1,uu____19630,t1) ->
               let uu___168_19644 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19644.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19644.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19644.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19644.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19645 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19647 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____19647 with
           | (univs1,binders,signature) ->
               let uu____19675 =
                 let uu____19684 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____19684 with
                 | (univs_opening,univs2) ->
                     let uu____19711 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____19711)
                  in
               (match uu____19675 with
                | (univs_opening,univs_closing) ->
                    let uu____19728 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____19734 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____19735 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____19734, uu____19735)  in
                    (match uu____19728 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____19757 =
                           match uu____19757 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____19775 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____19775 with
                                | (us1,t1) ->
                                    let uu____19786 =
                                      let uu____19791 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____19798 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____19791, uu____19798)  in
                                    (match uu____19786 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19811 =
                                           let uu____19816 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____19825 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____19816, uu____19825)  in
                                         (match uu____19811 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____19841 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____19841
                                                 in
                                              let uu____19842 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____19842 with
                                               | (uu____19863,uu____19864,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____19879 =
                                                       let uu____19880 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____19880
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____19879
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____19885 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____19885 with
                           | (uu____19898,uu____19899,t1) -> t1  in
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
                             | uu____19959 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____19976 =
                               let uu____19977 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____19977.FStar_Syntax_Syntax.n  in
                             match uu____19976 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20036 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____20065 =
                               let uu____20066 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____20066.FStar_Syntax_Syntax.n  in
                             match uu____20065 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20087) ->
                                 let uu____20108 = destruct_action_body body
                                    in
                                 (match uu____20108 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20153 ->
                                 let uu____20154 = destruct_action_body t  in
                                 (match uu____20154 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____20203 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____20203 with
                           | (action_univs,t) ->
                               let uu____20212 = destruct_action_typ_templ t
                                  in
                               (match uu____20212 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20253 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20253.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20253.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___170_20255 = ed  in
                           let uu____20256 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____20257 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____20258 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____20259 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____20260 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____20261 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____20262 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____20263 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____20264 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____20265 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____20266 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____20267 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____20268 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____20269 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20255.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20255.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20256;
                             FStar_Syntax_Syntax.bind_wp = uu____20257;
                             FStar_Syntax_Syntax.if_then_else = uu____20258;
                             FStar_Syntax_Syntax.ite_wp = uu____20259;
                             FStar_Syntax_Syntax.stronger = uu____20260;
                             FStar_Syntax_Syntax.close_wp = uu____20261;
                             FStar_Syntax_Syntax.assert_p = uu____20262;
                             FStar_Syntax_Syntax.assume_p = uu____20263;
                             FStar_Syntax_Syntax.null_wp = uu____20264;
                             FStar_Syntax_Syntax.trivial = uu____20265;
                             FStar_Syntax_Syntax.repr = uu____20266;
                             FStar_Syntax_Syntax.return_repr = uu____20267;
                             FStar_Syntax_Syntax.bind_repr = uu____20268;
                             FStar_Syntax_Syntax.actions = uu____20269
                           }  in
                         let uu___171_20272 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20272.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20272.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20272.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20272.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20289 =
            match uu___88_20289 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20316 = elim_uvars_aux_t env us [] t  in
                (match uu____20316 with
                 | (us1,uu____20340,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___172_20359 = sub_eff  in
            let uu____20360 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____20363 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20359.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20359.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20360;
              FStar_Syntax_Syntax.lift = uu____20363
            }  in
          let uu___173_20366 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20366.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20366.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20366.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20366.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20376 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____20376 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20410 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20410.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20410.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20410.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20410.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20421 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  