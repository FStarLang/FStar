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
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____22 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____26 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____30 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____46 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____50 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____54 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____62 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____66 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____118 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____122 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____126 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____130 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____138 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____142 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____146 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____150 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____154 -> false
  
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____188  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____415 -> false
  
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
    match projectee with | Univ _0 -> true | uu____517 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____528 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___74_547  ->
    match uu___74_547 with
    | Clos (uu____548,t,uu____550,uu____551) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____596 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____928 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____964 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____1000 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____1147 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1189 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1245 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1285 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1317 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1353 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1369 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____1394 .
    'Auu____1394 ->
      FStar_Range.range -> 'Auu____1394 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1500 = FStar_ST.op_Bang r  in
          match uu____1500 with
          | FStar_Pervasives_Native.Some uu____1600 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____1706 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____1706 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___75_1713  ->
    match uu___75_1713 with
    | Arg (c,uu____1715,uu____1716) ->
        let uu____1717 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1717
    | MemoLazy uu____1718 -> "MemoLazy"
    | Abs (uu____1725,bs,uu____1727,uu____1728,uu____1729) ->
        let uu____1734 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1734
    | UnivArgs uu____1739 -> "UnivArgs"
    | Match uu____1746 -> "Match"
    | App (uu____1753,t,uu____1755,uu____1756) ->
        let uu____1757 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1757
    | Meta (m,uu____1759) -> "Meta"
    | Let uu____1760 -> "Let"
    | Cfg uu____1769 -> "Cfg"
    | Debug (t,uu____1771) ->
        let uu____1772 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1772
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1780 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1780 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1796 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____1796 then f () else ()
  
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  ->
    fun f  ->
      let uu____1809 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops"))
         in
      if uu____1809 then f () else ()
  
let is_empty : 'Auu____1813 . 'Auu____1813 Prims.list -> Prims.bool =
  fun uu___76_1819  ->
    match uu___76_1819 with | [] -> true | uu____1822 -> false
  
let lookup_bvar :
  'Auu____1829 'Auu____1830 .
    ('Auu____1830,'Auu____1829) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1829
  =
  fun env  ->
    fun x  ->
      try
        let uu____1854 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____1854
      with
      | uu____1867 ->
          let uu____1868 =
            let uu____1869 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____1869  in
          failwith uu____1868
  
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
          let uu____1906 =
            FStar_List.fold_left
              (fun uu____1932  ->
                 fun u1  ->
                   match uu____1932 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1957 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1957 with
                        | (k_u,n1) ->
                            let uu____1972 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1972
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1906 with
          | (uu____1990,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2015 =
                   let uu____2016 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2016  in
                 match uu____2015 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2034 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2043 ->
                   let uu____2044 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____2044
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2050 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2059 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2068 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2075 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2075 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2092 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2092 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2100 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2108 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2108 with
                                  | (uu____2113,m) -> n1 <= m))
                           in
                        if uu____2100 then rest1 else us1
                    | uu____2118 -> us1)
               | uu____2123 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2127 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2127
           in
        let uu____2130 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____2130
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2132 = aux u  in
           match uu____2132 with
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
          (fun uu____2236  ->
             let uu____2237 = FStar_Syntax_Print.tag_of_term t  in
             let uu____2238 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2237
               uu____2238);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2245 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2247 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2272 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2273 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2274 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2275 ->
                  let uu____2292 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars)
                     in
                  if uu____2292
                  then
                    let uu____2293 =
                      let uu____2294 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____2295 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2294 uu____2295
                       in
                    failwith uu____2293
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2298 =
                    let uu____2299 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____2299  in
                  mk uu____2298 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2306 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2306
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2308 = lookup_bvar env x  in
                  (match uu____2308 with
                   | Univ uu____2311 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____2314,uu____2315) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2427 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2427 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____2455 =
                         let uu____2456 =
                           let uu____2473 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____2473)  in
                         FStar_Syntax_Syntax.Tm_abs uu____2456  in
                       mk uu____2455 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2504 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2504 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2546 =
                    let uu____2557 =
                      let uu____2564 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____2564]  in
                    closures_as_binders_delayed cfg env uu____2557  in
                  (match uu____2546 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____2582 =
                         let uu____2583 =
                           let uu____2590 =
                             let uu____2591 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____2591
                               FStar_Pervasives_Native.fst
                              in
                           (uu____2590, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____2583  in
                       mk uu____2582 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2682 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____2682
                    | FStar_Util.Inr c ->
                        let uu____2696 = close_comp cfg env c  in
                        FStar_Util.Inr uu____2696
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____2712 =
                    let uu____2713 =
                      let uu____2740 = closure_as_term_delayed cfg env t11
                         in
                      (uu____2740, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2713  in
                  mk uu____2712 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2791 =
                    let uu____2792 =
                      let uu____2799 = closure_as_term_delayed cfg env t'  in
                      let uu____2802 =
                        let uu____2803 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____2803  in
                      (uu____2799, uu____2802)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2792  in
                  mk uu____2791 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2863 =
                    let uu____2864 =
                      let uu____2871 = closure_as_term_delayed cfg env t'  in
                      let uu____2874 =
                        let uu____2875 =
                          let uu____2882 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____2882)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____2875  in
                      (uu____2871, uu____2874)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2864  in
                  mk uu____2863 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2901 =
                    let uu____2902 =
                      let uu____2909 = closure_as_term_delayed cfg env t'  in
                      let uu____2912 =
                        let uu____2913 =
                          let uu____2922 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____2922)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2913  in
                      (uu____2909, uu____2912)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2902  in
                  mk uu____2901 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2935 =
                    let uu____2936 =
                      let uu____2943 = closure_as_term_delayed cfg env t'  in
                      (uu____2943, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2936  in
                  mk uu____2935 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2983  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3002 =
                    let uu____3013 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3013
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3032 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___97_3044 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___97_3044.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___97_3044.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3032))
                     in
                  (match uu____3002 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___98_3060 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___98_3060.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___98_3060.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3071,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3130  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____3155 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3155
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3175  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____3197 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3197
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___99_3209 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___99_3209.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___99_3209.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___100_3210 = lb  in
                    let uu____3211 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___100_3210.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___100_3210.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3211
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3241  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____3330 =
                    match uu____3330 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3385 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3406 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3466  ->
                                        fun uu____3467  ->
                                          match (uu____3466, uu____3467) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3558 =
                                                norm_pat env3 p1  in
                                              (match uu____3558 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____3406 with
                               | (pats1,env3) ->
                                   ((let uu___101_3640 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___101_3640.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___102_3659 = x  in
                                let uu____3660 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3659.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3659.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3660
                                }  in
                              ((let uu___103_3674 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3674.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___104_3685 = x  in
                                let uu____3686 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___104_3685.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___104_3685.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3686
                                }  in
                              ((let uu___105_3700 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___105_3700.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___106_3716 = x  in
                                let uu____3717 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___106_3716.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___106_3716.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3717
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___107_3724 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___107_3724.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____3727 = norm_pat env1 pat  in
                        (match uu____3727 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3756 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____3756
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____3762 =
                    let uu____3763 =
                      let uu____3786 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____3786)  in
                    FStar_Syntax_Syntax.Tm_match uu____3763  in
                  mk uu____3762 t1.FStar_Syntax_Syntax.pos))

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
        | uu____3872 -> closure_as_term cfg env t

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
        | uu____3898 ->
            FStar_List.map
              (fun uu____3915  ->
                 match uu____3915 with
                 | (x,imp) ->
                     let uu____3934 = closure_as_term_delayed cfg env x  in
                     (uu____3934, imp)) args

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
        let uu____3948 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3997  ->
                  fun uu____3998  ->
                    match (uu____3997, uu____3998) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___108_4068 = b  in
                          let uu____4069 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___108_4068.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___108_4068.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4069
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____3948 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4162 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4175 = closure_as_term_delayed cfg env t  in
                 let uu____4176 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4175 uu____4176
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4189 = closure_as_term_delayed cfg env t  in
                 let uu____4190 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4189 uu____4190
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
                        (fun uu___77_4216  ->
                           match uu___77_4216 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4220 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____4220
                           | f -> f))
                    in
                 let uu____4224 =
                   let uu___109_4225 = c1  in
                   let uu____4226 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4226;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___109_4225.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4224)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___78_4236  ->
            match uu___78_4236 with
            | FStar_Syntax_Syntax.DECREASES uu____4237 -> false
            | uu____4240 -> true))

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
                   (fun uu___79_4258  ->
                      match uu___79_4258 with
                      | FStar_Syntax_Syntax.DECREASES uu____4259 -> false
                      | uu____4262 -> true))
               in
            let rc1 =
              let uu___110_4264 = rc  in
              let uu____4265 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___110_4264.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4265;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____4272 -> lopt

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
    let uu____4357 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4357  in
  let arg_as_bounded_int uu____4385 =
    match uu____4385 with
    | (a,uu____4397) ->
        let uu____4404 =
          let uu____4405 = FStar_Syntax_Subst.compress a  in
          uu____4405.FStar_Syntax_Syntax.n  in
        (match uu____4404 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4415;
                FStar_Syntax_Syntax.vars = uu____4416;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4418;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4419;_},uu____4420)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4459 =
               let uu____4464 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____4464)  in
             FStar_Pervasives_Native.Some uu____4459
         | uu____4469 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4509 = f a  in FStar_Pervasives_Native.Some uu____4509
    | uu____4510 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4558 = f a0 a1  in FStar_Pervasives_Native.Some uu____4558
    | uu____4559 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4601 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____4601)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4650 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____4650)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____4674 =
    match uu____4674 with
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
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4722 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____4722)) a429 a430)
     in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4750 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____4750)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4771 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____4771)) a436
             a437)
     in
  let binary_bool_op f =
    binary_op () (fun a438  -> (Obj.magic arg_as_bool) a438)
      (fun a439  ->
         fun a440  ->
           fun a441  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4799 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____4799)) a439
               a440 a441)
     in
  let binary_string_op f =
    binary_op () (fun a442  -> (Obj.magic arg_as_string) a442)
      (fun a443  ->
         fun a444  ->
           fun a445  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4827 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____4827))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4935 =
          let uu____4944 = as_a a  in
          let uu____4947 = as_b b  in (uu____4944, uu____4947)  in
        (match uu____4935 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4962 =
               let uu____4963 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____4963  in
             FStar_Pervasives_Native.Some uu____4962
         | uu____4964 -> FStar_Pervasives_Native.None)
    | uu____4973 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____4987 =
        let uu____4988 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____4988  in
      mk uu____4987 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____4998 =
      let uu____5001 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5001  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4998  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5033 =
      let uu____5034 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5034  in
    FStar_Syntax_Embeddings.embed_int rng uu____5033  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5052 = arg_as_string a1  in
        (match uu____5052 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5058 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5058 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5071 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5071
              | uu____5072 -> FStar_Pervasives_Native.None)
         | uu____5077 -> FStar_Pervasives_Native.None)
    | uu____5080 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5090 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5090  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5114 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5125 =
          let uu____5146 = arg_as_string fn  in
          let uu____5149 = arg_as_int from_line  in
          let uu____5152 = arg_as_int from_col  in
          let uu____5155 = arg_as_int to_line  in
          let uu____5158 = arg_as_int to_col  in
          (uu____5146, uu____5149, uu____5152, uu____5155, uu____5158)  in
        (match uu____5125 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5189 =
                 let uu____5190 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5191 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5190 uu____5191  in
               let uu____5192 =
                 let uu____5193 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5194 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5193 uu____5194  in
               FStar_Range.mk_range fn1 uu____5189 uu____5192  in
             let uu____5195 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____5195
         | uu____5200 -> FStar_Pervasives_Native.None)
    | uu____5221 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____5248)::(a1,uu____5250)::(a2,uu____5252)::[] ->
        let uu____5289 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____5289 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5302 -> FStar_Pervasives_Native.None)
    | uu____5303 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____5330)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5339 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____5363 =
      let uu____5378 =
        let uu____5393 =
          let uu____5408 =
            let uu____5423 =
              let uu____5438 =
                let uu____5453 =
                  let uu____5468 =
                    let uu____5483 =
                      let uu____5498 =
                        let uu____5513 =
                          let uu____5528 =
                            let uu____5543 =
                              let uu____5558 =
                                let uu____5573 =
                                  let uu____5588 =
                                    let uu____5603 =
                                      let uu____5618 =
                                        let uu____5633 =
                                          let uu____5648 =
                                            let uu____5663 =
                                              let uu____5678 =
                                                let uu____5691 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____5691,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447  ->
                                                        fun a448  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448)))
                                                 in
                                              let uu____5698 =
                                                let uu____5713 =
                                                  let uu____5726 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____5726,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450  ->
                                                          fun a451  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451)))
                                                   in
                                                let uu____5733 =
                                                  let uu____5748 =
                                                    let uu____5763 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____5763,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____5772 =
                                                    let uu____5789 =
                                                      let uu____5804 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____5804,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____5813 =
                                                      let uu____5830 =
                                                        let uu____5849 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____5849,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____5830]  in
                                                    uu____5789 :: uu____5813
                                                     in
                                                  uu____5748 :: uu____5772
                                                   in
                                                uu____5713 :: uu____5733  in
                                              uu____5678 :: uu____5698  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5663
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5648
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452  ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453  ->
                                                fun a454  ->
                                                  fun a455  ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____5633
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____5618
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____5603
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462  ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463  ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464  ->
                                          fun a465  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466  ->
                                          fun a467  ->
                                            fun a468  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____6066 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6066 y)) a466
                                                a467 a468)))
                                    :: uu____5588
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5573
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5558
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5543
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5528
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5513
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5498
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a469  -> (Obj.magic arg_as_int) a469)
                         (fun a470  ->
                            fun a471  ->
                              fun a472  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____6233 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____6233)) a470 a471 a472)))
                      :: uu____5483
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____6259 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____6259)) a474 a475 a476)))
                    :: uu____5468
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____6285 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____6285)) a478 a479 a480)))
                  :: uu____5453
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____6311 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____6311)) a482 a483 a484)))
                :: uu____5438
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5423
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5408
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5393
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5378
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5363
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____6464 =
        let uu____6465 =
          let uu____6466 = FStar_Syntax_Syntax.as_arg c  in [uu____6466]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6465  in
      uu____6464 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6516 =
                let uu____6529 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____6529, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6545  ->
                                    fun uu____6546  ->
                                      match (uu____6545, uu____6546) with
                                      | ((int_to_t1,x),(uu____6565,y)) ->
                                          let uu____6575 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____6575)) a486 a487 a488)))
                 in
              let uu____6576 =
                let uu____6591 =
                  let uu____6604 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____6604, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6620  ->
                                      fun uu____6621  ->
                                        match (uu____6620, uu____6621) with
                                        | ((int_to_t1,x),(uu____6640,y)) ->
                                            let uu____6650 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____6650)) a490 a491 a492)))
                   in
                let uu____6651 =
                  let uu____6666 =
                    let uu____6679 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____6679, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6695  ->
                                        fun uu____6696  ->
                                          match (uu____6695, uu____6696) with
                                          | ((int_to_t1,x),(uu____6715,y)) ->
                                              let uu____6725 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____6725)) a494 a495 a496)))
                     in
                  let uu____6726 =
                    let uu____6741 =
                      let uu____6754 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____6754, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6766  ->
                                        match uu____6766 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____6741]  in
                  uu____6666 :: uu____6726  in
                uu____6591 :: uu____6651  in
              uu____6516 :: uu____6576))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6880 =
                let uu____6893 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____6893, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6909  ->
                                    fun uu____6910  ->
                                      match (uu____6909, uu____6910) with
                                      | ((int_to_t1,x),(uu____6929,y)) ->
                                          let uu____6939 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____6939)) a501 a502 a503)))
                 in
              let uu____6940 =
                let uu____6955 =
                  let uu____6968 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____6968, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6984  ->
                                      fun uu____6985  ->
                                        match (uu____6984, uu____6985) with
                                        | ((int_to_t1,x),(uu____7004,y)) ->
                                            let uu____7014 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7014)) a505 a506 a507)))
                   in
                [uu____6955]  in
              uu____6880 :: uu____6940))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
  
let (equality_ops : primitive_step Prims.list) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____7104)::(a1,uu____7106)::(a2,uu____7108)::[] ->
        let uu____7145 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7145 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_7151 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_7151.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_7151.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_7155 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_7155.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_7155.FStar_Syntax_Syntax.vars)
                })
         | uu____7156 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7158)::uu____7159::(a1,uu____7161)::(a2,uu____7163)::[] ->
        let uu____7212 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7212 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_7218 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_7218.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_7218.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_7222 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_7222.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_7222.FStar_Syntax_Syntax.vars)
                })
         | uu____7223 -> FStar_Pervasives_Native.None)
    | uu____7224 -> failwith "Unexpected number of arguments"  in
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
      let uu____7243 =
        let uu____7244 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____7244 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____7243
    with | uu____7250 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____7254 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7254) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____7314  ->
           fun subst1  ->
             match uu____7314 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____7355,uu____7356)) ->
                      let uu____7415 = b  in
                      (match uu____7415 with
                       | (bv,uu____7423) ->
                           let uu____7424 =
                             let uu____7425 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____7425  in
                           if uu____7424
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____7430 = unembed_binder term1  in
                              match uu____7430 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7437 =
                                      let uu___115_7438 = bv  in
                                      let uu____7439 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___115_7438.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___115_7438.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7439
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____7437
                                     in
                                  let b_for_x =
                                    let uu____7443 =
                                      let uu____7450 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7450)
                                       in
                                    FStar_Syntax_Syntax.NT uu____7443  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___80_7459  ->
                                         match uu___80_7459 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7460,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7462;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7463;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7468 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____7469 -> subst1)) env []
  
let reduce_primops :
  'Auu____7486 'Auu____7487 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7487) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7486 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____7528 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps)
             in
          if uu____7528
          then tm
          else
            (let uu____7530 = FStar_Syntax_Util.head_and_args tm  in
             match uu____7530 with
             | (head1,args) ->
                 let uu____7567 =
                   let uu____7568 = FStar_Syntax_Util.un_uinst head1  in
                   uu____7568.FStar_Syntax_Syntax.n  in
                 (match uu____7567 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7572 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps
                         in
                      (match uu____7572 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7589  ->
                                   let uu____7590 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____7591 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____7598 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7590 uu____7591 uu____7598);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7603  ->
                                   let uu____7604 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7604);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7607  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____7609 =
                                 prim_step.interpretation psc args  in
                               match uu____7609 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7615  ->
                                         let uu____7616 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7616);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7622  ->
                                         let uu____7623 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____7624 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7623 uu____7624);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7625 ->
                           (log_primops cfg
                              (fun uu____7629  ->
                                 let uu____7630 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7630);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7634  ->
                            let uu____7635 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7635);
                       (match args with
                        | (a1,uu____7637)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7654 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7666  ->
                            let uu____7667 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7667);
                       (match args with
                        | (t,uu____7669)::(r,uu____7671)::[] ->
                            let uu____7698 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____7698 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___116_7702 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___116_7702.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___116_7702.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7705 -> tm))
                  | uu____7714 -> tm))
  
let reduce_equality :
  'Auu____7719 'Auu____7720 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7720) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7719 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___117_7758 = cfg  in
         {
           steps = [Primops];
           tcenv = (uu___117_7758.tcenv);
           delta_level = (uu___117_7758.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___117_7758.strong);
           memoize_lazy = (uu___117_7758.memoize_lazy);
           normalize_pure_lets = (uu___117_7758.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____7765 'Auu____7766 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7766) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7765 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____7808 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps)
             in
          if uu____7808
          then tm1
          else
            (let w t =
               let uu___118_7820 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___118_7820.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___118_7820.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7836;
                      FStar_Syntax_Syntax.vars = uu____7837;_},uu____7838)
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
                      FStar_Syntax_Syntax.pos = uu____7845;
                      FStar_Syntax_Syntax.vars = uu____7846;_},uu____7847)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7853 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____7858 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____7858
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7879 =
                 match uu____7879 with
                 | (t1,q) ->
                     let uu____7892 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____7892 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7920 -> (t1, q))
                  in
               let uu____7929 = FStar_Syntax_Util.head_and_args t  in
               match uu____7929 with
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
                         FStar_Syntax_Syntax.pos = uu____8026;
                         FStar_Syntax_Syntax.vars = uu____8027;_},uu____8028);
                    FStar_Syntax_Syntax.pos = uu____8029;
                    FStar_Syntax_Syntax.vars = uu____8030;_},args)
                 ->
                 let uu____8056 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8056
                 then
                   let uu____8057 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8057 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8112)::
                        (uu____8113,(arg,uu____8115))::[] ->
                        maybe_auto_squash arg
                    | (uu____8180,(arg,uu____8182))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8183)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____8248)::uu____8249::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8312::(FStar_Pervasives_Native.Some (false
                                   ),uu____8313)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8376 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____8392 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____8392
                    then
                      let uu____8393 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____8393 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8448)::uu____8449::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8512::(FStar_Pervasives_Native.Some (true
                                     ),uu____8513)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8576)::
                          (uu____8577,(arg,uu____8579))::[] ->
                          maybe_auto_squash arg
                      | (uu____8644,(arg,uu____8646))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8647)::[]
                          -> maybe_auto_squash arg
                      | uu____8712 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8728 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____8728
                       then
                         let uu____8729 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____8729 with
                         | uu____8784::(FStar_Pervasives_Native.Some (true
                                        ),uu____8785)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8848)::uu____8849::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8912)::
                             (uu____8913,(arg,uu____8915))::[] ->
                             maybe_auto_squash arg
                         | (uu____8980,(p,uu____8982))::(uu____8983,(q,uu____8985))::[]
                             ->
                             let uu____9050 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9050
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9052 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9068 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____9068
                          then
                            let uu____9069 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9069 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9124)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9163)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9202 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____9218 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____9218
                             then
                               match args with
                               | (t,uu____9220)::[] ->
                                   let uu____9237 =
                                     let uu____9238 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____9238.FStar_Syntax_Syntax.n  in
                                   (match uu____9237 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9241::[],body,uu____9243) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9270 -> tm1)
                                    | uu____9273 -> tm1)
                               | (uu____9274,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____9275))::
                                   (t,uu____9277)::[] ->
                                   let uu____9316 =
                                     let uu____9317 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____9317.FStar_Syntax_Syntax.n  in
                                   (match uu____9316 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____9320::[],body,uu____9322) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9349 -> tm1)
                                    | uu____9352 -> tm1)
                               | uu____9353 -> tm1
                             else
                               (let uu____9363 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____9363
                                then
                                  match args with
                                  | (t,uu____9365)::[] ->
                                      let uu____9382 =
                                        let uu____9383 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9383.FStar_Syntax_Syntax.n  in
                                      (match uu____9382 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9386::[],body,uu____9388)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9415 -> tm1)
                                       | uu____9418 -> tm1)
                                  | (uu____9419,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9420))::(t,uu____9422)::[] ->
                                      let uu____9461 =
                                        let uu____9462 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9462.FStar_Syntax_Syntax.n  in
                                      (match uu____9461 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9465::[],body,uu____9467)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9494 -> tm1)
                                       | uu____9497 -> tm1)
                                  | uu____9498 -> tm1
                                else
                                  (let uu____9508 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____9508
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9509;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9510;_},uu____9511)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9528;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9529;_},uu____9530)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9547 -> tm1
                                   else
                                     (let uu____9557 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____9557 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9577 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9587;
                    FStar_Syntax_Syntax.vars = uu____9588;_},args)
                 ->
                 let uu____9610 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____9610
                 then
                   let uu____9611 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____9611 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9666)::
                        (uu____9667,(arg,uu____9669))::[] ->
                        maybe_auto_squash arg
                    | (uu____9734,(arg,uu____9736))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9737)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9802)::uu____9803::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9866::(FStar_Pervasives_Native.Some (false
                                   ),uu____9867)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9930 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9946 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9946
                    then
                      let uu____9947 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9947 with
                      | (FStar_Pervasives_Native.Some (true ),uu____10002)::uu____10003::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10066::(FStar_Pervasives_Native.Some (true
                                      ),uu____10067)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____10130)::
                          (uu____10131,(arg,uu____10133))::[] ->
                          maybe_auto_squash arg
                      | (uu____10198,(arg,uu____10200))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____10201)::[]
                          -> maybe_auto_squash arg
                      | uu____10266 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____10282 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____10282
                       then
                         let uu____10283 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____10283 with
                         | uu____10338::(FStar_Pervasives_Native.Some (true
                                         ),uu____10339)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10402)::uu____10403::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10466)::
                             (uu____10467,(arg,uu____10469))::[] ->
                             maybe_auto_squash arg
                         | (uu____10534,(p,uu____10536))::(uu____10537,
                                                           (q,uu____10539))::[]
                             ->
                             let uu____10604 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____10604
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10606 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10622 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____10622
                          then
                            let uu____10623 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____10623 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10678)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10717)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10756 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10772 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____10772
                             then
                               match args with
                               | (t,uu____10774)::[] ->
                                   let uu____10791 =
                                     let uu____10792 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10792.FStar_Syntax_Syntax.n  in
                                   (match uu____10791 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10795::[],body,uu____10797) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10824 -> tm1)
                                    | uu____10827 -> tm1)
                               | (uu____10828,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10829))::
                                   (t,uu____10831)::[] ->
                                   let uu____10870 =
                                     let uu____10871 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10871.FStar_Syntax_Syntax.n  in
                                   (match uu____10870 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10874::[],body,uu____10876) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10903 -> tm1)
                                    | uu____10906 -> tm1)
                               | uu____10907 -> tm1
                             else
                               (let uu____10917 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10917
                                then
                                  match args with
                                  | (t,uu____10919)::[] ->
                                      let uu____10936 =
                                        let uu____10937 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10937.FStar_Syntax_Syntax.n  in
                                      (match uu____10936 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10940::[],body,uu____10942)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10969 -> tm1)
                                       | uu____10972 -> tm1)
                                  | (uu____10973,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10974))::(t,uu____10976)::[] ->
                                      let uu____11015 =
                                        let uu____11016 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11016.FStar_Syntax_Syntax.n  in
                                      (match uu____11015 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11019::[],body,uu____11021)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11048 -> tm1)
                                       | uu____11051 -> tm1)
                                  | uu____11052 -> tm1
                                else
                                  (let uu____11062 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____11062
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11063;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11064;_},uu____11065)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11082;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11083;_},uu____11084)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11101 -> tm1
                                   else
                                     (let uu____11111 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____11111 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____11131 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____11146 -> tm1)
  
let maybe_simplify :
  'Auu____11153 'Auu____11154 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11154) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11153 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          (let uu____11197 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380")
              in
           if uu____11197
           then
             let uu____11198 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11199 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____11198 uu____11199
           else ());
          tm'
  
let is_norm_request :
  'Auu____11205 .
    FStar_Syntax_Syntax.term -> 'Auu____11205 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11218 =
        let uu____11225 =
          let uu____11226 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11226.FStar_Syntax_Syntax.n  in
        (uu____11225, args)  in
      match uu____11218 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11232::uu____11233::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11237::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11242::uu____11243::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11246 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___81_11257  ->
    match uu___81_11257 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11263 =
          let uu____11266 =
            let uu____11267 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11267  in
          [uu____11266]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____11263
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11283 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____11283) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11321 =
          let uu____11324 =
            let uu____11329 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step
               in
            uu____11329 s  in
          FStar_All.pipe_right uu____11324 FStar_Util.must  in
        FStar_All.pipe_right uu____11321 tr_norm_steps  in
      match args with
      | uu____11354::(tm,uu____11356)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____11379)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____11394)::uu____11395::(tm,uu____11397)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
            let uu____11437 =
              let uu____11440 = full_norm steps  in parse_steps uu____11440
               in
            Beta :: uu____11437  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____11449 -> failwith "Impossible"
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___82_11466  ->
    match uu___82_11466 with
    | (App
        (uu____11469,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11470;
                       FStar_Syntax_Syntax.vars = uu____11471;_},uu____11472,uu____11473))::uu____11474
        -> true
    | uu____11481 -> false
  
let firstn :
  'Auu____11487 .
    Prims.int ->
      'Auu____11487 Prims.list ->
        ('Auu____11487 Prims.list,'Auu____11487 Prims.list)
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
          (uu____11523,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11524;
                         FStar_Syntax_Syntax.vars = uu____11525;_},uu____11526,uu____11527))::uu____11528
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11535 -> false
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            (let uu____11677 =
               FStar_TypeChecker_Env.debug cfg.tcenv
                 (FStar_Options.Other "NormDelayed")
                in
             if uu____11677
             then
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____11678 ->
                   let uu____11703 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11703
               | uu____11704 -> ()
             else ());
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11713  ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               let uu____11715 = FStar_Syntax_Print.tag_of_term t2  in
               let uu____11716 = FStar_Syntax_Print.term_to_string t2  in
               let uu____11717 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11724 =
                 let uu____11725 =
                   let uu____11728 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11728
                    in
                 stack_to_string uu____11725  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11715 uu____11716 uu____11717 uu____11724);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11751 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11752 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11753;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11754;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11757;
                 FStar_Syntax_Syntax.fv_delta = uu____11758;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11759;
                 FStar_Syntax_Syntax.fv_delta = uu____11760;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11761);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11769 = FStar_Syntax_Syntax.lid_of_fv fv  in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11769 ->
               let b = should_reify cfg stack  in
               (log cfg
                  (fun uu____11775  ->
                     let uu____11776 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____11777 = FStar_Util.string_of_bool b  in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11776 uu____11777);
                if b
                then
                  (let uu____11778 = FStar_List.tl stack  in
                   do_unfold_fv cfg env uu____11778 t1 fv)
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
                 let uu___119_11817 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___119_11817.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___119_11817.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11850 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____11850) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___120_11858 = cfg  in
                 let uu____11859 =
                   FStar_List.filter
                     (fun uu___83_11862  ->
                        match uu___83_11862 with
                        | UnfoldOnly uu____11863 -> false
                        | NoDeltaSteps  -> false
                        | uu____11866 -> true) cfg.steps
                    in
                 {
                   steps = uu____11859;
                   tcenv = (uu___120_11858.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___120_11858.primitive_steps);
                   strong = (uu___120_11858.strong);
                   memoize_lazy = (uu___120_11858.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11867 = get_norm_request (norm cfg' env []) args  in
               (match uu____11867 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11883 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___84_11888  ->
                                match uu___84_11888 with
                                | UnfoldUntil uu____11889 -> true
                                | UnfoldOnly uu____11890 -> true
                                | uu____11893 -> false))
                         in
                      if uu____11883
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___121_11898 = cfg  in
                      {
                        steps = s;
                        tcenv = (uu___121_11898.tcenv);
                        delta_level;
                        primitive_steps = (uu___121_11898.primitive_steps);
                        strong = (uu___121_11898.strong);
                        memoize_lazy = (uu___121_11898.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      let uu____11905 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms")
                         in
                      if uu____11905
                      then
                        let uu____11908 =
                          let uu____11909 =
                            let uu____11914 = FStar_Util.now ()  in
                            (t1, uu____11914)  in
                          Debug uu____11909  in
                        uu____11908 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11918 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11918
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11925 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____11925
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11928 =
                      let uu____11935 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11935, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11928  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___85_11948  ->
                         match uu___85_11948 with
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
                 let uu____11951 =
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
                 if uu____11951
                 then false
                 else
                   (let uu____11953 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___86_11960  ->
                              match uu___86_11960 with
                              | UnfoldOnly uu____11961 -> true
                              | UnfoldAttr uu____11964 -> true
                              | uu____11965 -> false))
                       in
                    match uu____11953 with
                    | FStar_Pervasives_Native.Some uu____11966 ->
                        let attr_eq a a' =
                          let uu____11974 = FStar_Syntax_Util.eq_tm a a'  in
                          match uu____11974 with
                          | FStar_Syntax_Util.Equal  -> true
                          | uu____11975 -> false  in
                        should_delta &&
                          (FStar_List.fold_left
                             (fun acc  ->
                                fun x  ->
                                  match x with
                                  | UnfoldOnly lids ->
                                      acc ||
                                        (FStar_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid f)
                                           lids)
                                  | UnfoldAttr attr ->
                                      let uu____11985 =
                                        FStar_TypeChecker_Env.lookup_attrs_of_lid
                                          cfg.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      (match uu____11985 with
                                       | FStar_Pervasives_Native.Some attrs
                                           ->
                                           acc ||
                                             (FStar_Util.for_some
                                                (attr_eq attr) attrs)
                                       | uu____11995 -> acc)
                                  | uu____12000 -> acc) false cfg.steps)
                    | uu____12001 -> should_delta)
                  in
               (log cfg
                  (fun uu____12009  ->
                     let uu____12010 = FStar_Syntax_Print.term_to_string t1
                        in
                     let uu____12011 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos
                        in
                     let uu____12012 =
                       FStar_Util.string_of_bool should_delta1  in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____12010 uu____12011 uu____12012);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12015 = lookup_bvar env x  in
               (match uu____12015 with
                | Univ uu____12018 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____12067 = FStar_ST.op_Bang r  in
                      (match uu____12067 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12237  ->
                                 let uu____12238 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12239 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12238
                                   uu____12239);
                            (let uu____12240 =
                               let uu____12241 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____12241.FStar_Syntax_Syntax.n  in
                             match uu____12240 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12244 ->
                                 norm cfg env2 stack t'
                             | uu____12261 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12409)::uu____12410 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12419)::uu____12420 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12430,uu____12431))::stack_rest ->
                    (match c with
                     | Univ uu____12435 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12444 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12465  ->
                                    let uu____12466 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12466);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12506  ->
                                    let uu____12507 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12507);
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
                       (fun uu____12637  ->
                          let uu____12638 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12638);
                     norm cfg env stack1 t1)
                | (Debug uu____12639)::uu____12640 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12647 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12647
                    else
                      (let uu____12649 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12649 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12691  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12719 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12719
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12729 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12729)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12734 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12734.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12734.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12735 -> lopt  in
                           (log cfg
                              (fun uu____12741  ->
                                 let uu____12742 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12742);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___123_12751 = cfg  in
                               {
                                 steps = (uu___123_12751.steps);
                                 tcenv = (uu___123_12751.tcenv);
                                 delta_level = (uu___123_12751.delta_level);
                                 primitive_steps =
                                   (uu___123_12751.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12751.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12751.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12762)::uu____12763 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12770 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12770
                    else
                      (let uu____12772 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12772 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12814  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12842 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12842
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12852 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12852)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12857 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12857.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12857.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12858 -> lopt  in
                           (log cfg
                              (fun uu____12864  ->
                                 let uu____12865 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12865);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___123_12874 = cfg  in
                               {
                                 steps = (uu___123_12874.steps);
                                 tcenv = (uu___123_12874.tcenv);
                                 delta_level = (uu___123_12874.delta_level);
                                 primitive_steps =
                                   (uu___123_12874.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12874.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_12874.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12885)::uu____12886 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12897 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12897
                    else
                      (let uu____12899 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12899 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12941  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12969 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12969
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12979 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12979)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12984 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12984.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12984.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12985 -> lopt  in
                           (log cfg
                              (fun uu____12991  ->
                                 let uu____12992 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12992);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___123_13001 = cfg  in
                               {
                                 steps = (uu___123_13001.steps);
                                 tcenv = (uu___123_13001.tcenv);
                                 delta_level = (uu___123_13001.delta_level);
                                 primitive_steps =
                                   (uu___123_13001.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_13001.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_13001.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13012)::uu____13013 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13024 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13024
                    else
                      (let uu____13026 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13026 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13068  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13096 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____13096
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13106 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13106)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_13111 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_13111.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_13111.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13112 -> lopt  in
                           (log cfg
                              (fun uu____13118  ->
                                 let uu____13119 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13119);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___123_13128 = cfg  in
                               {
                                 steps = (uu___123_13128.steps);
                                 tcenv = (uu___123_13128.tcenv);
                                 delta_level = (uu___123_13128.delta_level);
                                 primitive_steps =
                                   (uu___123_13128.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_13128.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_13128.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13139)::uu____13140 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13155 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13155
                    else
                      (let uu____13157 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13157 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13199  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13227 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____13227
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13237 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13237)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_13242 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_13242.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_13242.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13243 -> lopt  in
                           (log cfg
                              (fun uu____13249  ->
                                 let uu____13250 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13250);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___123_13259 = cfg  in
                               {
                                 steps = (uu___123_13259.steps);
                                 tcenv = (uu___123_13259.tcenv);
                                 delta_level = (uu___123_13259.delta_level);
                                 primitive_steps =
                                   (uu___123_13259.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_13259.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_13259.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____13270 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13270
                    else
                      (let uu____13272 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13272 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13314  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____13342 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____13342
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____13352 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13352)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_13357 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_13357.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_13357.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13358 -> lopt  in
                           (log cfg
                              (fun uu____13364  ->
                                 let uu____13365 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13365);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___123_13374 = cfg  in
                               {
                                 steps = (uu___123_13374.steps);
                                 tcenv = (uu___123_13374.tcenv);
                                 delta_level = (uu___123_13374.delta_level);
                                 primitive_steps =
                                   (uu___123_13374.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_13374.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___123_13374.normalize_pure_lets)
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
                      (fun uu____13423  ->
                         fun stack1  ->
                           match uu____13423 with
                           | (a,aq) ->
                               let uu____13435 =
                                 let uu____13436 =
                                   let uu____13443 =
                                     let uu____13444 =
                                       let uu____13475 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13475, false)  in
                                     Clos uu____13444  in
                                   (uu____13443, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13436  in
                               uu____13435 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13611  ->
                     let uu____13612 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13612);
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
                             ((let uu___124_13648 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___124_13648.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___124_13648.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13649 ->
                      let uu____13654 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13654)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13657 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13657 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13688 =
                          let uu____13689 =
                            let uu____13696 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___125_13698 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___125_13698.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___125_13698.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13696)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13689  in
                        mk uu____13688 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13717 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13717
               else
                 (let uu____13719 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13719 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13727 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13751  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13727 c1  in
                      let t2 =
                        let uu____13773 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13773 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               FStar_List.contains Unascribe cfg.steps ->
               norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13884)::uu____13885 ->
                    (log cfg
                       (fun uu____13896  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13897)::uu____13898 ->
                    (log cfg
                       (fun uu____13909  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13910,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13911;
                                   FStar_Syntax_Syntax.vars = uu____13912;_},uu____13913,uu____13914))::uu____13915
                    ->
                    (log cfg
                       (fun uu____13924  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13925)::uu____13926 ->
                    (log cfg
                       (fun uu____13937  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13938 ->
                    (log cfg
                       (fun uu____13941  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13945  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13962 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13962
                         | FStar_Util.Inr c ->
                             let uu____13970 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13970
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13983 =
                               let uu____13984 =
                                 let uu____14011 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14011, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13984
                                in
                             mk uu____13983 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14030 ->
                           let uu____14031 =
                             let uu____14032 =
                               let uu____14033 =
                                 let uu____14060 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14060, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14033
                                in
                             mk uu____14032 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14031))))
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
                         let uu____14170 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14170 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___126_14190 = cfg  in
                               let uu____14191 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___126_14190.steps);
                                 tcenv = uu____14191;
                                 delta_level = (uu___126_14190.delta_level);
                                 primitive_steps =
                                   (uu___126_14190.primitive_steps);
                                 strong = (uu___126_14190.strong);
                                 memoize_lazy = (uu___126_14190.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___126_14190.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14196 =
                                 let uu____14197 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14197  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14196
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___127_14200 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___127_14200.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___127_14200.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             }))
                  in
               let uu____14201 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14201
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14212,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14213;
                               FStar_Syntax_Syntax.lbunivs = uu____14214;
                               FStar_Syntax_Syntax.lbtyp = uu____14215;
                               FStar_Syntax_Syntax.lbeff = uu____14216;
                               FStar_Syntax_Syntax.lbdef = uu____14217;_}::uu____14218),uu____14219)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14255 =
                 (let uu____14258 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____14258) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____14260 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)
                             in
                          Prims.op_Negation uu____14260)))
                  in
               if uu____14255
               then
                 let binder =
                   let uu____14262 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14262  in
                 let env1 =
                   let uu____14272 =
                     let uu____14279 =
                       let uu____14280 =
                         let uu____14311 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14311,
                           false)
                          in
                       Clos uu____14280  in
                     ((FStar_Pervasives_Native.Some binder), uu____14279)  in
                   uu____14272 :: env  in
                 (log cfg
                    (fun uu____14456  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if FStar_List.contains Weak cfg.steps
                 then
                   (log cfg
                      (fun uu____14460  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14461 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14461))
                 else
                   (let uu____14463 =
                      let uu____14468 =
                        let uu____14469 =
                          let uu____14470 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14470
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14469]  in
                      FStar_Syntax_Subst.open_term uu____14468 body  in
                    match uu____14463 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14479  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14487 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14487  in
                            FStar_Util.Inl
                              (let uu___128_14497 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___128_14497.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___128_14497.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14500  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___129_14502 = lb  in
                             let uu____14503 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___129_14502.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___129_14502.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14503
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14538  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___130_14561 = cfg  in
                             {
                               steps = (uu___130_14561.steps);
                               tcenv = (uu___130_14561.tcenv);
                               delta_level = (uu___130_14561.delta_level);
                               primitive_steps =
                                 (uu___130_14561.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___130_14561.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___130_14561.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14564  ->
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
               let uu____14581 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14581 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14617 =
                               let uu___131_14618 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_14618.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_14618.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14617  in
                           let uu____14619 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14619 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14645 =
                                   FStar_List.map (fun uu____14661  -> dummy)
                                     lbs1
                                    in
                                 let uu____14662 =
                                   let uu____14671 =
                                     FStar_List.map
                                       (fun uu____14691  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14671 env  in
                                 FStar_List.append uu____14645 uu____14662
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14715 =
                                       let uu___132_14716 = rc  in
                                       let uu____14717 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___132_14716.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14717;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___132_14716.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14715
                                 | uu____14724 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___133_14728 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___133_14728.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___133_14728.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
                      let uu____14738 =
                        FStar_List.map (fun uu____14754  -> dummy) lbs2  in
                      FStar_List.append uu____14738 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14762 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14762 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___134_14778 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___134_14778.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___134_14778.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14805 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14805
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14824 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14900  ->
                        match uu____14900 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___135_15021 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___135_15021.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___135_15021.FStar_Syntax_Syntax.sort)
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
               (match uu____14824 with
                | (rec_env,memos,uu____15338) ->
                    let uu____15391 =
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
                             let uu____15780 =
                               let uu____15787 =
                                 let uu____15788 =
                                   let uu____15819 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15819, false)
                                    in
                                 Clos uu____15788  in
                               (FStar_Pervasives_Native.None, uu____15787)
                                in
                             uu____15780 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15981  ->
                     let uu____15982 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15982);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16004 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16006::uu____16007 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16012) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____16013 ->
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
                             | uu____16044 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16058 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16058
                              | uu____16069 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16073 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16099 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16117 ->
                    let uu____16134 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains CheckNoUvars)
                       in
                    if uu____16134
                    then
                      let uu____16135 =
                        let uu____16136 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16137 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16136 uu____16137
                         in
                      failwith uu____16135
                    else rebuild cfg env stack t2
                | uu____16139 -> norm cfg env stack t2))

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
              let uu____16148 = FStar_Syntax_Syntax.range_of_fv f  in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____16148  in
            let uu____16149 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            match uu____16149 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____16162  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____16173  ->
                      let uu____16174 = FStar_Syntax_Print.term_to_string t0
                         in
                      let uu____16175 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16174
                        uu____16175);
                 (let t1 =
                    let uu____16177 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____16179 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac)
                            in
                         Prims.op_Negation uu____16179)
                       in
                    if uu____16177
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
                    | (UnivArgs (us',uu____16189))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env)
                           in
                        norm cfg env1 stack1 t1
                    | uu____16244 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____16247 ->
                        let uu____16250 =
                          let uu____16251 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____16251
                           in
                        failwith uu____16250
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
                let uu____16272 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations)
                   in
                if uu____16272
                then
                  let uu___136_16273 = cfg  in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___136_16273.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___136_16273.primitive_steps);
                    strong = (uu___136_16273.strong);
                    memoize_lazy = (uu___136_16273.memoize_lazy);
                    normalize_pure_lets =
                      (uu___136_16273.normalize_pure_lets)
                  }
                else
                  (let uu___137_16275 = cfg  in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___137_16275.tcenv);
                     delta_level = (uu___137_16275.delta_level);
                     primitive_steps = (uu___137_16275.primitive_steps);
                     strong = (uu___137_16275.strong);
                     memoize_lazy = (uu___137_16275.memoize_lazy);
                     normalize_pure_lets =
                       (uu___137_16275.normalize_pure_lets)
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
                  (fun uu____16305  ->
                     let uu____16306 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16307 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16306
                       uu____16307);
                (let uu____16308 =
                   let uu____16309 = FStar_Syntax_Subst.compress head2  in
                   uu____16309.FStar_Syntax_Syntax.n  in
                 match uu____16308 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16327 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16327 with
                      | (uu____16328,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16334 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16342 =
                                   let uu____16343 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16343.FStar_Syntax_Syntax.n  in
                                 match uu____16342 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16349,uu____16350))
                                     ->
                                     let uu____16359 =
                                       let uu____16360 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16360.FStar_Syntax_Syntax.n  in
                                     (match uu____16359 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16366,msrc,uu____16368))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16377 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16377
                                      | uu____16378 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16379 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16380 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16380 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___138_16385 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___138_16385.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___138_16385.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___138_16385.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      }  in
                                    let uu____16386 = FStar_List.tl stack  in
                                    let uu____16387 =
                                      let uu____16388 =
                                        let uu____16391 =
                                          let uu____16392 =
                                            let uu____16405 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16405)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16392
                                           in
                                        FStar_Syntax_Syntax.mk uu____16391
                                         in
                                      uu____16388
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16386 uu____16387
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16421 =
                                      let uu____16422 = is_return body  in
                                      match uu____16422 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16426;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16427;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16432 -> false  in
                                    if uu____16421
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
                                         let uu____16455 =
                                           let uu____16458 =
                                             let uu____16459 =
                                               let uu____16476 =
                                                 let uu____16479 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16479]  in
                                               (uu____16476, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16459
                                              in
                                           FStar_Syntax_Syntax.mk uu____16458
                                            in
                                         uu____16455
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16495 =
                                           let uu____16496 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16496.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16495 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16502::uu____16503::[])
                                             ->
                                             let uu____16510 =
                                               let uu____16513 =
                                                 let uu____16514 =
                                                   let uu____16521 =
                                                     let uu____16524 =
                                                       let uu____16525 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16525
                                                        in
                                                     let uu____16526 =
                                                       let uu____16529 =
                                                         let uu____16530 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16530
                                                          in
                                                       [uu____16529]  in
                                                     uu____16524 ::
                                                       uu____16526
                                                      in
                                                   (bind1, uu____16521)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16514
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16513
                                                in
                                             uu____16510
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16538 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____16544 =
                                           let uu____16547 =
                                             let uu____16548 =
                                               let uu____16563 =
                                                 let uu____16566 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16567 =
                                                   let uu____16570 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____16571 =
                                                     let uu____16574 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16575 =
                                                       let uu____16578 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____16579 =
                                                         let uu____16582 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16583 =
                                                           let uu____16586 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16586]  in
                                                         uu____16582 ::
                                                           uu____16583
                                                          in
                                                       uu____16578 ::
                                                         uu____16579
                                                        in
                                                     uu____16574 ::
                                                       uu____16575
                                                      in
                                                   uu____16570 :: uu____16571
                                                    in
                                                 uu____16566 :: uu____16567
                                                  in
                                               (bind_inst, uu____16563)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16548
                                              in
                                           FStar_Syntax_Syntax.mk uu____16547
                                            in
                                         uu____16544
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16598  ->
                                            let uu____16599 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16600 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16599 uu____16600);
                                       (let uu____16601 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16601 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16625 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16625 with
                      | (uu____16626,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16661 =
                                  let uu____16662 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16662.FStar_Syntax_Syntax.n  in
                                match uu____16661 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16668) -> t2
                                | uu____16673 -> head3  in
                              let uu____16674 =
                                let uu____16675 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16675.FStar_Syntax_Syntax.n  in
                              match uu____16674 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16681 -> FStar_Pervasives_Native.None
                               in
                            let uu____16682 = maybe_extract_fv head3  in
                            match uu____16682 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16692 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16692
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____16697 = maybe_extract_fv head4
                                     in
                                  match uu____16697 with
                                  | FStar_Pervasives_Native.Some uu____16702
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16703 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____16708 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16723 =
                              match uu____16723 with
                              | (e,q) ->
                                  let uu____16730 =
                                    let uu____16731 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16731.FStar_Syntax_Syntax.n  in
                                  (match uu____16730 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____16746 -> false)
                               in
                            let uu____16747 =
                              let uu____16748 =
                                let uu____16755 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16755 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16748
                               in
                            if uu____16747
                            then
                              let uu____16760 =
                                let uu____16761 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16761
                                 in
                              failwith uu____16760
                            else ());
                           (let uu____16763 = maybe_unfold_action head_app
                               in
                            match uu____16763 with
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
                                   (fun uu____16804  ->
                                      let uu____16805 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16806 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16805 uu____16806);
                                 (let uu____16807 = FStar_List.tl stack  in
                                  norm cfg env uu____16807 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16809) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16833 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16833  in
                     (log cfg
                        (fun uu____16837  ->
                           let uu____16838 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16838);
                      (let uu____16839 = FStar_List.tl stack  in
                       norm cfg env uu____16839 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____16841) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16966  ->
                               match uu____16966 with
                               | (pat,wopt,tm) ->
                                   let uu____17014 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17014)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____17046 = FStar_List.tl stack  in
                     norm cfg env uu____17046 tm
                 | uu____17047 -> fallback ())

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
              (fun uu____17061  ->
                 let uu____17062 = FStar_Ident.string_of_lid msrc  in
                 let uu____17063 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17064 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17062
                   uu____17063 uu____17064);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____17066 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17066 with
               | (uu____17067,return_repr) ->
                   let return_inst =
                     let uu____17076 =
                       let uu____17077 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17077.FStar_Syntax_Syntax.n  in
                     match uu____17076 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17083::[]) ->
                         let uu____17090 =
                           let uu____17093 =
                             let uu____17094 =
                               let uu____17101 =
                                 let uu____17104 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17104]  in
                               (return_tm, uu____17101)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17094  in
                           FStar_Syntax_Syntax.mk uu____17093  in
                         uu____17090 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17112 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17115 =
                     let uu____17118 =
                       let uu____17119 =
                         let uu____17134 =
                           let uu____17137 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17138 =
                             let uu____17141 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17141]  in
                           uu____17137 :: uu____17138  in
                         (return_inst, uu____17134)  in
                       FStar_Syntax_Syntax.Tm_app uu____17119  in
                     FStar_Syntax_Syntax.mk uu____17118  in
                   uu____17115 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____17150 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____17150 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17153 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17153
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17154;
                     FStar_TypeChecker_Env.mtarget = uu____17155;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17156;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17171 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17171
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17172;
                     FStar_TypeChecker_Env.mtarget = uu____17173;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17174;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17198 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____17199 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____17198 t FStar_Syntax_Syntax.tun uu____17199)

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
                (fun uu____17255  ->
                   match uu____17255 with
                   | (a,imp) ->
                       let uu____17266 = norm cfg env [] a  in
                       (uu____17266, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___139_17280 = comp  in
            let uu____17281 =
              let uu____17282 =
                let uu____17291 = norm cfg env [] t  in
                let uu____17292 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17291, uu____17292)  in
              FStar_Syntax_Syntax.Total uu____17282  in
            {
              FStar_Syntax_Syntax.n = uu____17281;
              FStar_Syntax_Syntax.pos =
                (uu___139_17280.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_17280.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___140_17307 = comp  in
            let uu____17308 =
              let uu____17309 =
                let uu____17318 = norm cfg env [] t  in
                let uu____17319 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17318, uu____17319)  in
              FStar_Syntax_Syntax.GTotal uu____17309  in
            {
              FStar_Syntax_Syntax.n = uu____17308;
              FStar_Syntax_Syntax.pos =
                (uu___140_17307.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___140_17307.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____17371  ->
                      match uu____17371 with
                      | (a,i) ->
                          let uu____17382 = norm cfg env [] a  in
                          (uu____17382, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___87_17393  ->
                      match uu___87_17393 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17397 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____17397
                      | f -> f))
               in
            let uu___141_17401 = comp  in
            let uu____17402 =
              let uu____17403 =
                let uu___142_17404 = ct  in
                let uu____17405 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____17406 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____17409 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____17405;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___142_17404.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____17406;
                  FStar_Syntax_Syntax.effect_args = uu____17409;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____17403  in
            {
              FStar_Syntax_Syntax.n = uu____17402;
              FStar_Syntax_Syntax.pos =
                (uu___141_17401.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___141_17401.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17420  ->
        match uu____17420 with
        | (x,imp) ->
            let uu____17423 =
              let uu___143_17424 = x  in
              let uu____17425 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___143_17424.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___143_17424.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17425
              }  in
            (uu____17423, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17431 =
          FStar_List.fold_left
            (fun uu____17449  ->
               fun b  ->
                 match uu____17449 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17431 with | (nbs,uu____17489) -> FStar_List.rev nbs

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
            let uu____17505 =
              let uu___144_17506 = rc  in
              let uu____17507 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___144_17506.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17507;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___144_17506.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17505
        | uu____17514 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17527  ->
               let uu____17528 = FStar_Syntax_Print.tag_of_term t  in
               let uu____17529 = FStar_Syntax_Print.term_to_string t  in
               let uu____17530 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____17537 =
                 let uu____17538 =
                   let uu____17541 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17541
                    in
                 stack_to_string uu____17538  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____17528 uu____17529 uu____17530 uu____17537);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____17571 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms")
                    in
                 if uu____17571
                 then
                   let time_now = FStar_Util.now ()  in
                   let uu____17573 =
                     let uu____17574 =
                       let uu____17575 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____17575  in
                     FStar_Util.string_of_int uu____17574  in
                   let uu____17580 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____17581 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17573 uu____17580 uu____17581
                 else ());
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____17687  ->
                     let uu____17688 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17688);
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
               let uu____17724 =
                 let uu___145_17725 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___145_17725.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___145_17725.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____17724
           | (Arg (Univ uu____17726,uu____17727,uu____17728))::uu____17729 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17732,uu____17733))::uu____17734 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____17750),aq,r))::stack1 ->
               (log cfg
                  (fun uu____17803  ->
                     let uu____17804 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____17804);
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
                  (let uu____17814 = FStar_ST.op_Bang m  in
                   match uu____17814 with
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
                   | FStar_Pervasives_Native.Some (uu____18081,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____18128 =
                 log cfg
                   (fun uu____18132  ->
                      let uu____18133 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____18133);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____18137 =
                 let uu____18138 = FStar_Syntax_Subst.compress t1  in
                 uu____18138.FStar_Syntax_Syntax.n  in
               (match uu____18137 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____18165 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____18165  in
                    (log cfg
                       (fun uu____18169  ->
                          let uu____18170 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____18170);
                     (let uu____18171 = FStar_List.tl stack  in
                      norm cfg env1 uu____18171 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____18172);
                       FStar_Syntax_Syntax.pos = uu____18173;
                       FStar_Syntax_Syntax.vars = uu____18174;_},(e,uu____18176)::[])
                    -> norm cfg env1 stack' e
                | uu____18205 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18225  ->
                     let uu____18226 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18226);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____18231 =
                   log cfg
                     (fun uu____18236  ->
                        let uu____18237 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____18238 =
                          let uu____18239 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18256  ->
                                    match uu____18256 with
                                    | (p,uu____18266,uu____18267) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____18239
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18237 uu____18238);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps)
                       in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___88_18284  ->
                                match uu___88_18284 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18285 -> false))
                         in
                      let steps' = [Exclude Zeta]  in
                      let uu___146_18289 = cfg  in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___146_18289.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___146_18289.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___146_18289.memoize_lazy);
                        normalize_pure_lets =
                          (uu___146_18289.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18321 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18342 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18402  ->
                                    fun uu____18403  ->
                                      match (uu____18402, uu____18403) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18494 = norm_pat env3 p1
                                             in
                                          (match uu____18494 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____18342 with
                           | (pats1,env3) ->
                               ((let uu___147_18576 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___147_18576.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___148_18595 = x  in
                            let uu____18596 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_18595.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_18595.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18596
                            }  in
                          ((let uu___149_18610 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___149_18610.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___150_18621 = x  in
                            let uu____18622 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___150_18621.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___150_18621.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18622
                            }  in
                          ((let uu___151_18636 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___151_18636.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___152_18652 = x  in
                            let uu____18653 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_18652.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_18652.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18653
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___153_18660 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___153_18660.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18670 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18684 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____18684 with
                                  | (p,wopt,e) ->
                                      let uu____18704 = norm_pat env1 p  in
                                      (match uu____18704 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18729 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18729
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____18735 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____18735)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18745) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18750 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18751;
                         FStar_Syntax_Syntax.fv_delta = uu____18752;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18753;
                         FStar_Syntax_Syntax.fv_delta = uu____18754;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18755);_}
                       -> true
                   | uu____18762 -> false  in
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
                   let uu____18907 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____18907 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____18994 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____19033 ->
                                 let uu____19034 =
                                   let uu____19035 = is_cons head1  in
                                   Prims.op_Negation uu____19035  in
                                 FStar_Util.Inr uu____19034)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____19060 =
                              let uu____19061 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____19061.FStar_Syntax_Syntax.n  in
                            (match uu____19060 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____19079 ->
                                 let uu____19080 =
                                   let uu____19081 = is_cons head1  in
                                   Prims.op_Negation uu____19081  in
                                 FStar_Util.Inr uu____19080))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____19150)::rest_a,(p1,uu____19153)::rest_p) ->
                       let uu____19197 = matches_pat t2 p1  in
                       (match uu____19197 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19246 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19352 = matches_pat scrutinee1 p1  in
                       (match uu____19352 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19392  ->
                                  let uu____19393 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____19394 =
                                    let uu____19395 =
                                      FStar_List.map
                                        (fun uu____19405  ->
                                           match uu____19405 with
                                           | (uu____19410,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____19395
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19393 uu____19394);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19441  ->
                                       match uu____19441 with
                                       | (bv,t2) ->
                                           let uu____19464 =
                                             let uu____19471 =
                                               let uu____19474 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____19474
                                                in
                                             let uu____19475 =
                                               let uu____19476 =
                                                 let uu____19507 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____19507, false)
                                                  in
                                               Clos uu____19476  in
                                             (uu____19471, uu____19475)  in
                                           uu____19464 :: env2) env1 s
                                 in
                              let uu____19676 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____19676)))
                    in
                 let uu____19677 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota))
                    in
                 if uu____19677
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___89_19698  ->
                match uu___89_19698 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____19702 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____19708 -> d  in
      let uu____19711 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____19713 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations)
              in
           Prims.op_Negation uu____19713)
         in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____19711
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
            let uu___154_19738 = config s e  in
            {
              steps = (uu___154_19738.steps);
              tcenv = (uu___154_19738.tcenv);
              delta_level = (uu___154_19738.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___154_19738.strong);
              memoize_lazy = (uu___154_19738.memoize_lazy);
              normalize_pure_lets = (uu___154_19738.normalize_pure_lets)
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
      fun t  -> let uu____19763 = config s e  in norm_comp uu____19763 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____19776 = config [] env  in norm_universe uu____19776 [] u
  
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
        let uu____19794 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19794  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____19801 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___155_19820 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___155_19820.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___155_19820.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____19827 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____19827
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
                  let uu___156_19836 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___156_19836.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___156_19836.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___156_19836.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___157_19838 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___157_19838.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___157_19838.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___157_19838.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___157_19838.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___158_19839 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___158_19839.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___158_19839.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____19841 -> c
  
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
        let uu____19853 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19853  in
      let uu____19860 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____19860
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____19864  ->
                 let uu____19865 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____19865)
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
            ((let uu____19882 =
                let uu____19887 =
                  let uu____19888 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19888
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19887)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____19882);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19899 = config [AllowUnboundUniverses] env  in
          norm_comp uu____19899 [] c
        with
        | e ->
            ((let uu____19912 =
                let uu____19917 =
                  let uu____19918 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19918
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19917)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____19912);
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
                   let uu____19955 =
                     let uu____19956 =
                       let uu____19963 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____19963)  in
                     FStar_Syntax_Syntax.Tm_refine uu____19956  in
                   mk uu____19955 t01.FStar_Syntax_Syntax.pos
               | uu____19968 -> t2)
          | uu____19969 -> t2  in
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
        let uu____20009 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____20009 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____20038 ->
                 let uu____20045 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____20045 with
                  | (actuals,uu____20055,uu____20056) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____20070 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____20070 with
                         | (binders,args) ->
                             let uu____20087 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____20087
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
      | uu____20095 ->
          let uu____20096 = FStar_Syntax_Util.head_and_args t  in
          (match uu____20096 with
           | (head1,args) ->
               let uu____20133 =
                 let uu____20134 = FStar_Syntax_Subst.compress head1  in
                 uu____20134.FStar_Syntax_Syntax.n  in
               (match uu____20133 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____20137,thead) ->
                    let uu____20163 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____20163 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____20205 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___163_20213 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___163_20213.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___163_20213.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___163_20213.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___163_20213.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___163_20213.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___163_20213.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___163_20213.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___163_20213.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___163_20213.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___163_20213.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___163_20213.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___163_20213.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___163_20213.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___163_20213.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___163_20213.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___163_20213.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___163_20213.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___163_20213.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___163_20213.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___163_20213.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___163_20213.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___163_20213.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___163_20213.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___163_20213.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___163_20213.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___163_20213.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___163_20213.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___163_20213.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___163_20213.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___163_20213.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___163_20213.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___163_20213.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____20205 with
                            | (uu____20214,ty,uu____20216) ->
                                eta_expand_with_type env t ty))
                | uu____20217 ->
                    let uu____20218 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___164_20226 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___164_20226.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___164_20226.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___164_20226.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___164_20226.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___164_20226.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___164_20226.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___164_20226.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___164_20226.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___164_20226.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___164_20226.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___164_20226.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___164_20226.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___164_20226.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___164_20226.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___164_20226.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___164_20226.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___164_20226.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___164_20226.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___164_20226.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___164_20226.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___164_20226.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___164_20226.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___164_20226.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___164_20226.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___164_20226.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___164_20226.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___164_20226.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___164_20226.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___164_20226.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___164_20226.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___164_20226.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___164_20226.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____20218 with
                     | (uu____20227,ty,uu____20229) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___165_20286 = x  in
      let uu____20287 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___165_20286.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___165_20286.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____20287
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____20290 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____20315 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____20316 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____20317 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____20318 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____20325 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____20326 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___166_20354 = rc  in
          let uu____20355 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____20362 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___166_20354.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____20355;
            FStar_Syntax_Syntax.residual_flags = uu____20362
          }  in
        let uu____20365 =
          let uu____20366 =
            let uu____20383 = elim_delayed_subst_binders bs  in
            let uu____20390 = elim_delayed_subst_term t2  in
            let uu____20391 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____20383, uu____20390, uu____20391)  in
          FStar_Syntax_Syntax.Tm_abs uu____20366  in
        mk1 uu____20365
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____20420 =
          let uu____20421 =
            let uu____20434 = elim_delayed_subst_binders bs  in
            let uu____20441 = elim_delayed_subst_comp c  in
            (uu____20434, uu____20441)  in
          FStar_Syntax_Syntax.Tm_arrow uu____20421  in
        mk1 uu____20420
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____20454 =
          let uu____20455 =
            let uu____20462 = elim_bv bv  in
            let uu____20463 = elim_delayed_subst_term phi  in
            (uu____20462, uu____20463)  in
          FStar_Syntax_Syntax.Tm_refine uu____20455  in
        mk1 uu____20454
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____20486 =
          let uu____20487 =
            let uu____20502 = elim_delayed_subst_term t2  in
            let uu____20503 = elim_delayed_subst_args args  in
            (uu____20502, uu____20503)  in
          FStar_Syntax_Syntax.Tm_app uu____20487  in
        mk1 uu____20486
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___167_20567 = p  in
              let uu____20568 =
                let uu____20569 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____20569  in
              {
                FStar_Syntax_Syntax.v = uu____20568;
                FStar_Syntax_Syntax.p =
                  (uu___167_20567.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___168_20571 = p  in
              let uu____20572 =
                let uu____20573 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____20573  in
              {
                FStar_Syntax_Syntax.v = uu____20572;
                FStar_Syntax_Syntax.p =
                  (uu___168_20571.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___169_20580 = p  in
              let uu____20581 =
                let uu____20582 =
                  let uu____20589 = elim_bv x  in
                  let uu____20590 = elim_delayed_subst_term t0  in
                  (uu____20589, uu____20590)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____20582  in
              {
                FStar_Syntax_Syntax.v = uu____20581;
                FStar_Syntax_Syntax.p =
                  (uu___169_20580.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___170_20609 = p  in
              let uu____20610 =
                let uu____20611 =
                  let uu____20624 =
                    FStar_List.map
                      (fun uu____20647  ->
                         match uu____20647 with
                         | (x,b) ->
                             let uu____20660 = elim_pat x  in
                             (uu____20660, b)) pats
                     in
                  (fv, uu____20624)  in
                FStar_Syntax_Syntax.Pat_cons uu____20611  in
              {
                FStar_Syntax_Syntax.v = uu____20610;
                FStar_Syntax_Syntax.p =
                  (uu___170_20609.FStar_Syntax_Syntax.p)
              }
          | uu____20673 -> p  in
        let elim_branch uu____20695 =
          match uu____20695 with
          | (pat,wopt,t3) ->
              let uu____20721 = elim_pat pat  in
              let uu____20724 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____20727 = elim_delayed_subst_term t3  in
              (uu____20721, uu____20724, uu____20727)
           in
        let uu____20732 =
          let uu____20733 =
            let uu____20756 = elim_delayed_subst_term t2  in
            let uu____20757 = FStar_List.map elim_branch branches  in
            (uu____20756, uu____20757)  in
          FStar_Syntax_Syntax.Tm_match uu____20733  in
        mk1 uu____20732
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____20866 =
          match uu____20866 with
          | (tc,topt) ->
              let uu____20901 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____20911 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____20911
                | FStar_Util.Inr c ->
                    let uu____20913 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____20913
                 in
              let uu____20914 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____20901, uu____20914)
           in
        let uu____20923 =
          let uu____20924 =
            let uu____20951 = elim_delayed_subst_term t2  in
            let uu____20952 = elim_ascription a  in
            (uu____20951, uu____20952, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____20924  in
        mk1 uu____20923
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___171_20997 = lb  in
          let uu____20998 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____21001 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___171_20997.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___171_20997.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____20998;
            FStar_Syntax_Syntax.lbeff =
              (uu___171_20997.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____21001
          }  in
        let uu____21004 =
          let uu____21005 =
            let uu____21018 =
              let uu____21025 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____21025)  in
            let uu____21034 = elim_delayed_subst_term t2  in
            (uu____21018, uu____21034)  in
          FStar_Syntax_Syntax.Tm_let uu____21005  in
        mk1 uu____21004
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____21067 =
          let uu____21068 =
            let uu____21085 = elim_delayed_subst_term t2  in
            (uv, uu____21085)  in
          FStar_Syntax_Syntax.Tm_uvar uu____21068  in
        mk1 uu____21067
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____21102 =
          let uu____21103 =
            let uu____21110 = elim_delayed_subst_term t2  in
            let uu____21111 = elim_delayed_subst_meta md  in
            (uu____21110, uu____21111)  in
          FStar_Syntax_Syntax.Tm_meta uu____21103  in
        mk1 uu____21102

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___90_21118  ->
         match uu___90_21118 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____21122 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____21122
         | f -> f) flags1

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____21143 =
          let uu____21144 =
            let uu____21153 = elim_delayed_subst_term t  in
            (uu____21153, uopt)  in
          FStar_Syntax_Syntax.Total uu____21144  in
        mk1 uu____21143
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____21166 =
          let uu____21167 =
            let uu____21176 = elim_delayed_subst_term t  in
            (uu____21176, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____21167  in
        mk1 uu____21166
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___172_21181 = ct  in
          let uu____21182 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____21185 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____21194 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___172_21181.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___172_21181.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____21182;
            FStar_Syntax_Syntax.effect_args = uu____21185;
            FStar_Syntax_Syntax.flags = uu____21194
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___91_21197  ->
    match uu___91_21197 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____21209 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____21209
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____21242 =
          let uu____21249 = elim_delayed_subst_term t  in (m, uu____21249)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____21242
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____21257 =
          let uu____21266 = elim_delayed_subst_term t  in
          (m1, m2, uu____21266)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____21257
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____21274 =
          let uu____21283 = elim_delayed_subst_term t  in (d, s, uu____21283)
           in
        FStar_Syntax_Syntax.Meta_alien uu____21274
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____21306  ->
         match uu____21306 with
         | (t,q) ->
             let uu____21317 = elim_delayed_subst_term t  in (uu____21317, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____21337  ->
         match uu____21337 with
         | (x,q) ->
             let uu____21348 =
               let uu___173_21349 = x  in
               let uu____21350 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___173_21349.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___173_21349.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____21350
               }  in
             (uu____21348, q)) bs

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
            | (uu____21426,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____21432,FStar_Util.Inl t) ->
                let uu____21438 =
                  let uu____21441 =
                    let uu____21442 =
                      let uu____21455 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____21455)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____21442  in
                  FStar_Syntax_Syntax.mk uu____21441  in
                uu____21438 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____21459 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____21459 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____21487 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____21542 ->
                    let uu____21543 =
                      let uu____21552 =
                        let uu____21553 = FStar_Syntax_Subst.compress t4  in
                        uu____21553.FStar_Syntax_Syntax.n  in
                      (uu____21552, tc)  in
                    (match uu____21543 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____21578) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____21615) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____21654,FStar_Util.Inl uu____21655) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____21678 -> failwith "Impossible")
                 in
              (match uu____21487 with
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
          let uu____21783 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____21783 with
          | (univ_names1,binders1,tc) ->
              let uu____21841 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____21841)
  
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
          let uu____21876 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____21876 with
          | (univ_names1,binders1,tc) ->
              let uu____21936 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____21936)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____21969 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____21969 with
           | (univ_names1,binders1,typ1) ->
               let uu___174_21997 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_21997.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_21997.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_21997.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_21997.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___175_22018 = s  in
          let uu____22019 =
            let uu____22020 =
              let uu____22029 = FStar_List.map (elim_uvars env) sigs  in
              (uu____22029, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____22020  in
          {
            FStar_Syntax_Syntax.sigel = uu____22019;
            FStar_Syntax_Syntax.sigrng =
              (uu___175_22018.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___175_22018.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___175_22018.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___175_22018.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____22046 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22046 with
           | (univ_names1,uu____22064,typ1) ->
               let uu___176_22078 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___176_22078.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___176_22078.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___176_22078.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___176_22078.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____22084 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22084 with
           | (univ_names1,uu____22102,typ1) ->
               let uu___177_22116 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___177_22116.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___177_22116.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___177_22116.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___177_22116.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____22150 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____22150 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____22173 =
                            let uu____22174 =
                              let uu____22175 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____22175  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____22174
                             in
                          elim_delayed_subst_term uu____22173  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___178_22178 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___178_22178.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___178_22178.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        }))
             in
          let uu___179_22179 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___179_22179.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___179_22179.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___179_22179.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___179_22179.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___180_22191 = s  in
          let uu____22192 =
            let uu____22193 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____22193  in
          {
            FStar_Syntax_Syntax.sigel = uu____22192;
            FStar_Syntax_Syntax.sigrng =
              (uu___180_22191.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___180_22191.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___180_22191.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___180_22191.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____22197 = elim_uvars_aux_t env us [] t  in
          (match uu____22197 with
           | (us1,uu____22215,t1) ->
               let uu___181_22229 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___181_22229.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___181_22229.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___181_22229.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___181_22229.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22230 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22232 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____22232 with
           | (univs1,binders,signature) ->
               let uu____22260 =
                 let uu____22269 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____22269 with
                 | (univs_opening,univs2) ->
                     let uu____22296 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____22296)
                  in
               (match uu____22260 with
                | (univs_opening,univs_closing) ->
                    let uu____22313 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____22319 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____22320 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____22319, uu____22320)  in
                    (match uu____22313 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____22342 =
                           match uu____22342 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____22360 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____22360 with
                                | (us1,t1) ->
                                    let uu____22371 =
                                      let uu____22376 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____22383 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____22376, uu____22383)  in
                                    (match uu____22371 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____22396 =
                                           let uu____22401 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____22410 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____22401, uu____22410)  in
                                         (match uu____22396 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____22426 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____22426
                                                 in
                                              let uu____22427 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____22427 with
                                               | (uu____22448,uu____22449,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____22464 =
                                                       let uu____22465 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____22465
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____22464
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____22470 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____22470 with
                           | (uu____22483,uu____22484,t1) -> t1  in
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
                             | uu____22544 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____22561 =
                               let uu____22562 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____22562.FStar_Syntax_Syntax.n  in
                             match uu____22561 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____22621 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____22650 =
                               let uu____22651 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____22651.FStar_Syntax_Syntax.n  in
                             match uu____22650 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____22672) ->
                                 let uu____22693 = destruct_action_body body
                                    in
                                 (match uu____22693 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____22738 ->
                                 let uu____22739 = destruct_action_body t  in
                                 (match uu____22739 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____22788 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____22788 with
                           | (action_univs,t) ->
                               let uu____22797 = destruct_action_typ_templ t
                                  in
                               (match uu____22797 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___182_22838 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___182_22838.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___182_22838.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___183_22840 = ed  in
                           let uu____22841 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____22842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____22843 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____22844 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____22845 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____22846 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____22847 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____22848 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____22849 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____22850 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____22851 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____22852 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____22853 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____22854 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___183_22840.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___183_22840.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____22841;
                             FStar_Syntax_Syntax.bind_wp = uu____22842;
                             FStar_Syntax_Syntax.if_then_else = uu____22843;
                             FStar_Syntax_Syntax.ite_wp = uu____22844;
                             FStar_Syntax_Syntax.stronger = uu____22845;
                             FStar_Syntax_Syntax.close_wp = uu____22846;
                             FStar_Syntax_Syntax.assert_p = uu____22847;
                             FStar_Syntax_Syntax.assume_p = uu____22848;
                             FStar_Syntax_Syntax.null_wp = uu____22849;
                             FStar_Syntax_Syntax.trivial = uu____22850;
                             FStar_Syntax_Syntax.repr = uu____22851;
                             FStar_Syntax_Syntax.return_repr = uu____22852;
                             FStar_Syntax_Syntax.bind_repr = uu____22853;
                             FStar_Syntax_Syntax.actions = uu____22854
                           }  in
                         let uu___184_22857 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___184_22857.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___184_22857.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___184_22857.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___184_22857.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___92_22874 =
            match uu___92_22874 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____22901 = elim_uvars_aux_t env us [] t  in
                (match uu____22901 with
                 | (us1,uu____22925,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___185_22944 = sub_eff  in
            let uu____22945 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____22948 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___185_22944.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___185_22944.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____22945;
              FStar_Syntax_Syntax.lift = uu____22948
            }  in
          let uu___186_22951 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___186_22951.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___186_22951.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___186_22951.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___186_22951.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____22961 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____22961 with
           | (univ_names1,binders1,comp1) ->
               let uu___187_22995 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___187_22995.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___187_22995.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___187_22995.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___187_22995.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____23006 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  