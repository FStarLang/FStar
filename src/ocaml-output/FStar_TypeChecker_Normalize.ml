open Prims
type step =
<<<<<<< HEAD
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
let uu___is_Beta : step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____19 -> false 
let uu___is_Iota : step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____24 -> false 
let uu___is_Zeta : step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____29 -> false 
let uu___is_Exclude : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
  
let __proj__Exclude__item___0 : step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let uu___is_WHNF : step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____48 -> false 
let uu___is_Primops : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____53 -> false
  
let uu___is_Eager_unfolding : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
  
let uu___is_Inlining : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____63 -> false
  
let uu___is_NoDeltaSteps : step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____68 -> false
  
let uu___is_UnfoldUntil : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____74 -> false
  
let __proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let uu___is_UnfoldOnly : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____90 -> false
  
let __proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let uu___is_UnfoldTac : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____109 -> false
  
let uu___is_PureSubtermsWithinComputations : step -> Prims.bool =
=======
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
let (uu___is_Beta :step -> Prims.bool)=
  fun projectee  -> match projectee with | Beta  -> true | uu____19 -> false
let (uu___is_Iota :step -> Prims.bool)=
  fun projectee  -> match projectee with | Iota  -> true | uu____24 -> false
let (uu___is_Zeta :step -> Prims.bool)=
  fun projectee  -> match projectee with | Zeta  -> true | uu____29 -> false
let (uu___is_Exclude :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
let (__proj__Exclude__item___0 :step -> step)=
  fun projectee  -> match projectee with | Exclude _0 -> _0
let (uu___is_WHNF :step -> Prims.bool)=
  fun projectee  -> match projectee with | WHNF  -> true | uu____48 -> false
let (uu___is_Primops :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | Primops  -> true | uu____53 -> false
let (uu___is_Eager_unfolding :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
let (uu___is_Inlining :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____63 -> false
let (uu___is_NoDeltaSteps :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____68 -> false
let (uu___is_UnfoldUntil :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____74 -> false
let (__proj__UnfoldUntil__item___0 :step -> FStar_Syntax_Syntax.delta_depth)=
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____90 -> false
let (__proj__UnfoldOnly__item___0 :step -> FStar_Ident.lid Prims.list)=
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldTac :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____109 -> false
let (uu___is_PureSubtermsWithinComputations :step -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____114 -> false
<<<<<<< HEAD
  
let uu___is_Simplify : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____119 -> false
  
let uu___is_EraseUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____124 -> false
  
let uu___is_AllowUnboundUniverses : step -> Prims.bool =
=======
let (uu___is_Simplify :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____119 -> false
let (uu___is_EraseUniverses :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____124 -> false
let (uu___is_AllowUnboundUniverses :step -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____129 -> false
<<<<<<< HEAD
  
let uu___is_Reify : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
  
let uu___is_CompressUvars : step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____139 -> false
  
let uu___is_NoFullNorm : step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____144 -> false
  
let uu___is_CheckNoUvars : step -> Prims.bool =
=======
let (uu___is_Reify :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
let (uu___is_CompressUvars :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____139 -> false
let (uu___is_NoFullNorm :step -> Prims.bool)=
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____144 -> false
let (uu___is_CheckNoUvars :step -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____149 -> false
  
type steps = step Prims.list
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  strong_reduction_ok: Prims.bool ;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args ->
<<<<<<< HEAD
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    }
let __proj__Mkprimitive_step__item__name : primitive_step -> FStar_Ident.lid
  =
=======
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}
let (__proj__Mkprimitive_step__item__name
  :primitive_step -> FStar_Ident.lid)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__name
<<<<<<< HEAD
  
let __proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int =
=======
let (__proj__Mkprimitive_step__item__arity :primitive_step -> Prims.int)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__arity
<<<<<<< HEAD
  
let __proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool =
=======
let (__proj__Mkprimitive_step__item__strong_reduction_ok
  :primitive_step -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
<<<<<<< HEAD
  
let __proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
=======
let (__proj__Mkprimitive_step__item__interpretation
  :primitive_step ->
     FStar_Range.range ->
       FStar_Syntax_Syntax.args ->
         FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
  
type closure =
  | Clos of
  (closure Prims.list,FStar_Syntax_Syntax.term,(closure Prims.list,FStar_Syntax_Syntax.term)
                                                 FStar_Pervasives_Native.tuple2
                                                 FStar_Syntax_Syntax.memo,
<<<<<<< HEAD
  Prims.bool) FStar_Pervasives_Native.tuple4 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let uu___is_Clos : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____303 -> false
  
let __proj__Clos__item___0 :
  closure ->
    (closure Prims.list,FStar_Syntax_Syntax.term,(closure Prims.list,
                                                   FStar_Syntax_Syntax.term)
                                                   FStar_Pervasives_Native.tuple2
                                                   FStar_Syntax_Syntax.memo,
      Prims.bool) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let uu___is_Univ : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____371 -> false
  
let __proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let uu___is_Dummy : closure -> Prims.bool =
=======
  Prims.bool) FStar_Pervasives_Native.tuple4
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy
let (uu___is_Clos :closure -> Prims.bool)=
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____303 -> false
let (__proj__Clos__item___0
  :closure ->
     (closure Prims.list,FStar_Syntax_Syntax.term,(closure Prims.list,
                                                    FStar_Syntax_Syntax.term)
                                                    FStar_Pervasives_Native.tuple2
                                                    FStar_Syntax_Syntax.memo,
       Prims.bool) FStar_Pervasives_Native.tuple4)=
  fun projectee  -> match projectee with | Clos _0 -> _0
let (uu___is_Univ :closure -> Prims.bool)=
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____371 -> false
let (__proj__Univ__item___0 :closure -> FStar_Syntax_Syntax.universe)=
  fun projectee  -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy :closure -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____384 -> false
  
type env = closure Prims.list
<<<<<<< HEAD
let closure_to_string : closure -> Prims.string =
=======
let (closure_to_string :closure -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun uu___145_390  ->
    match uu___145_390 with
    | Clos (uu____391,t,uu____393,uu____394) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____415 -> "Univ"
    | Dummy  -> "dummy"
  
type cfg =
  {
<<<<<<< HEAD
  steps: steps ;
  tcenv: FStar_TypeChecker_Env.env ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step Prims.list }
let __proj__Mkcfg__item__steps : cfg -> steps =
=======
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}
let (__proj__Mkcfg__item__steps :cfg -> steps)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__steps
<<<<<<< HEAD
  
let __proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env =
=======
let (__proj__Mkcfg__item__tcenv :cfg -> FStar_TypeChecker_Env.env)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__tcenv
<<<<<<< HEAD
  
let __proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
=======
let (__proj__Mkcfg__item__delta_level
  :cfg -> FStar_TypeChecker_Env.delta_level Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__delta_level
<<<<<<< HEAD
  
let __proj__Mkcfg__item__primitive_steps : cfg -> primitive_step Prims.list =
=======
let (__proj__Mkcfg__item__primitive_steps :cfg -> primitive_step Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} ->
        __fname__primitive_steps
  
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list
type subst_t = FStar_Syntax_Syntax.subst_elt Prims.list
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
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Steps of
  (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                     Prims.list)
<<<<<<< HEAD
  FStar_Pervasives_Native.tuple3 
  | Debug of FStar_Syntax_Syntax.term 
let uu___is_Arg : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____632 -> false
  
let __proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let uu___is_UnivArgs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____670 -> false
  
let __proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let uu___is_MemoLazy : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____708 -> false
  
let __proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let uu___is_Match : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____767 -> false
  
let __proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0 
let uu___is_Abs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____811 -> false
  
let __proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let uu___is_App : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____867 -> false
  
let __proj__App__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Meta : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____903 -> false
  
let __proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let uu___is_Let : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____937 -> false
  
let __proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Steps : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____985 -> false
  
let __proj__Steps__item___0 :
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0 
let uu___is_Debug : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1029 -> false
  
let __proj__Debug__item___0 : stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let mk :
  'Auu____1046 .
    'Auu____1046 ->
      FStar_Range.range -> 'Auu____1046 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo :
  'Auu____1203 'Auu____1204 .
    ('Auu____1204 FStar_Pervasives_Native.option,'Auu____1203) FStar_ST.mref
      -> 'Auu____1204 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1499 = FStar_ST.op_Bang r  in
      match uu____1499 with
      | FStar_Pervasives_Native.Some uu____1600 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
  
let env_to_string : closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1707 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____1707 (FStar_String.concat "; ")
  
let stack_elt_to_string : stack_elt -> Prims.string =
  fun uu___146_1715  ->
    match uu___146_1715 with
    | Arg (c,uu____1717,uu____1718) ->
        let uu____1719 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1719
    | MemoLazy uu____1720 -> "MemoLazy"
    | Abs (uu____1727,bs,uu____1729,uu____1730,uu____1731) ->
        let uu____1736 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1736
    | UnivArgs uu____1741 -> "UnivArgs"
    | Match uu____1748 -> "Match"
    | App (t,uu____1756,uu____1757) ->
        let uu____1758 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1758
    | Meta (m,uu____1760) -> "Meta"
    | Let uu____1761 -> "Let"
    | Steps (uu____1770,uu____1771,uu____1772) -> "Steps"
    | Debug t ->
        let uu____1782 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1782
  
let stack_to_string : stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1791 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1791 (FStar_String.concat "; ")
  
let log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1809 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____1809 then f () else ()
  
let is_empty : 'Auu____1815 . 'Auu____1815 Prims.list -> Prims.bool =
  fun uu___147_1821  ->
    match uu___147_1821 with | [] -> true | uu____1824 -> false
  
let lookup_bvar :
  'Auu____1833 .
    'Auu____1833 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1833
  =
=======
  FStar_Pervasives_Native.tuple3
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2
let (uu___is_Arg :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____636 -> false
let (__proj__Arg__item___0
  :stack_elt ->
     (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____674 -> false
let (__proj__UnivArgs__item___0
  :stack_elt ->
     (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____712 -> false
let (__proj__MemoLazy__item___0
  :stack_elt ->
     (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
       FStar_Syntax_Syntax.memo)=
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____771 -> false
let (__proj__Match__item___0
  :stack_elt ->
     (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Match _0 -> _0
let (uu___is_Abs :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____815 -> false
let (__proj__Abs__item___0
  :stack_elt ->
     (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                            FStar_Pervasives_Native.option,
       FStar_Range.range) FStar_Pervasives_Native.tuple5)=
  fun projectee  -> match projectee with | Abs _0 -> _0
let (uu___is_App :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | App _0 -> true | uu____871 -> false
let (__proj__App__item___0
  :stack_elt ->
     (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | App _0 -> _0
let (uu___is_Meta :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____907 -> false
let (__proj__Meta__item___0
  :stack_elt ->
     (FStar_Syntax_Syntax.metadata,FStar_Range.range)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Meta _0 -> _0
let (uu___is_Let :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____941 -> false
let (__proj__Let__item___0
  :stack_elt ->
     (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,
       FStar_Range.range) FStar_Pervasives_Native.tuple4)=
  fun projectee  -> match projectee with | Let _0 -> _0
let (uu___is_Steps :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____989 -> false
let (__proj__Steps__item___0
  :stack_elt ->
     (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                        Prims.list)
       FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Steps _0 -> _0
let (uu___is_Debug :stack_elt -> Prims.bool)=
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1037 -> false
let (__proj__Debug__item___0
  :stack_elt ->
     (FStar_Syntax_Syntax.term,FStar_Util.time)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk :
  'Auu____1066 .
    'Auu____1066 ->
      FStar_Range.range -> 'Auu____1066 FStar_Syntax_Syntax.syntax=
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo :
  'Auu____1223 'Auu____1224 .
    ('Auu____1224 FStar_Pervasives_Native.option,'Auu____1223) FStar_ST.mref
      -> 'Auu____1224 -> Prims.unit=
  fun r  ->
    fun t  ->
      let uu____1519 = FStar_ST.op_Bang r in
      match uu____1519 with
      | FStar_Pervasives_Native.Some uu____1620 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let (env_to_string :closure Prims.list -> Prims.string)=
  fun env  ->
    let uu____1727 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1727 (FStar_String.concat "; ")
let (stack_elt_to_string :stack_elt -> Prims.string)=
  fun uu___146_1735  ->
    match uu___146_1735 with
    | Arg (c,uu____1737,uu____1738) ->
        let uu____1739 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1739
    | MemoLazy uu____1740 -> "MemoLazy"
    | Abs (uu____1747,bs,uu____1749,uu____1750,uu____1751) ->
        let uu____1756 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1756
    | UnivArgs uu____1761 -> "UnivArgs"
    | Match uu____1768 -> "Match"
    | App (t,uu____1776,uu____1777) ->
        let uu____1778 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1778
    | Meta (m,uu____1780) -> "Meta"
    | Let uu____1781 -> "Let"
    | Steps (uu____1790,uu____1791,uu____1792) -> "Steps"
    | Debug (t,uu____1802) ->
        let uu____1803 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1803
let (stack_to_string :stack_elt Prims.list -> Prims.string)=
  fun s  ->
    let uu____1812 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1812 (FStar_String.concat "; ")
let (log :cfg -> (Prims.unit -> Prims.unit) -> Prims.unit)=
  fun cfg  ->
    fun f  ->
      let uu____1830 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1830 then f () else ()
let is_empty : 'Auu____1836 . 'Auu____1836 Prims.list -> Prims.bool=
  fun uu___147_1842  ->
    match uu___147_1842 with | [] -> true | uu____1845 -> false
let lookup_bvar :
  'Auu____1854 .
    'Auu____1854 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1854=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
<<<<<<< HEAD
      | uu____1852 ->
          let uu____1853 =
            let uu____1854 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____1854  in
          failwith uu____1853
  
let downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
=======
      | uu____1873 ->
          let uu____1874 =
            let uu____1875 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1875 in
          failwith uu____1874
let (downgrade_ghost_effect_name
  :FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let norm_universe :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
=======
let (norm_universe
  :cfg ->
     closure Prims.list ->
       FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
<<<<<<< HEAD
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____1899 =
=======
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____1920 =
>>>>>>> taramana_pointers_with_codes_modifies
            FStar_List.fold_left
              (fun uu____1946  ->
                 fun u1  ->
                   match uu____1946 with
                   | (cur_kernel,cur_max,out) ->
<<<<<<< HEAD
                       let uu____1950 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1950 with
                        | (k_u,n1) ->
                            let uu____1965 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1965
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1899 with
          | (uu____1983,u1,out) -> FStar_List.rev (u1 :: out)  in
=======
                       let uu____1971 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1971 with
                        | (k_u,n1) ->
                            let uu____1986 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1986
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1920 with
          | (uu____2004,u1,out) -> FStar_List.rev (u1 :: out) in
>>>>>>> taramana_pointers_with_codes_modifies
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
<<<<<<< HEAD
                 let uu____2008 = FStar_List.nth env x  in
                 match uu____2008 with
=======
                 let uu____2029 = FStar_List.nth env x in
                 match uu____2029 with
>>>>>>> taramana_pointers_with_codes_modifies
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2033 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2042 ->
                   let uu____2043 =
                     FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____2022
=======
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2043
>>>>>>> taramana_pointers_with_codes_modifies
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2049 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2058 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2067 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
<<<<<<< HEAD
                let uu____2053 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2053 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2070 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2070 with
=======
                let uu____2074 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2074 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2091 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2091 with
>>>>>>> taramana_pointers_with_codes_modifies
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2099 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
<<<<<<< HEAD
                                  let uu____2086 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2086 with
                                  | (uu____2091,m) -> n1 <= m))
                           in
                        if uu____2078 then rest1 else us1
                    | uu____2096 -> us1)
               | uu____2101 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2105 = aux u3  in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2105
           in
        let uu____2108 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____2108
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2110 = aux u  in
           match uu____2110 with
=======
                                  let uu____2107 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2107 with
                                  | (uu____2112,m) -> n1 <= m)) in
                        if uu____2099 then rest1 else us1
                    | uu____2117 -> us1)
               | uu____2122 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2126 = aux u3 in
              FStar_List.map (fun _0_42  -> FStar_Syntax_Syntax.U_succ _0_42)
                uu____2126 in
        let uu____2129 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2129
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2131 = aux u in
           match uu____2131 with
>>>>>>> taramana_pointers_with_codes_modifies
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
<<<<<<< HEAD
  
let rec closure_as_term :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
let rec (closure_as_term
  :cfg ->
     closure Prims.list ->
       FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
<<<<<<< HEAD
          (fun uu____2230  ->
             let uu____2231 = FStar_Syntax_Print.tag_of_term t  in
             let uu____2232 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2231
               uu____2232);
=======
          (fun uu____2251  ->
             let uu____2252 = FStar_Syntax_Print.tag_of_term t in
             let uu____2253 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2252
               uu____2253);
>>>>>>> taramana_pointers_with_codes_modifies
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
<<<<<<< HEAD
         | uu____2233 ->
             let t1 = FStar_Syntax_Subst.compress t  in
=======
         | uu____2254 ->
             let t1 = FStar_Syntax_Subst.compress t in
>>>>>>> taramana_pointers_with_codes_modifies
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2258 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2283 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2284 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2285 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2286 ->
                  let uu____2303 =
                    FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                      (FStar_List.contains CheckNoUvars)
                     in
                  if uu____2282
=======
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2303
>>>>>>> taramana_pointers_with_codes_modifies
                  then
                    let uu____2304 =
                      let uu____2305 =
                        FStar_Range.string_of_range
<<<<<<< HEAD
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____2285 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2284 uu____2285
                       in
                    failwith uu____2283
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2288 =
                    let uu____2289 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____2289  in
                  mk uu____2288 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2296 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2296
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2298 = lookup_bvar env x  in
                  (match uu____2298 with
                   | Univ uu____2299 ->
=======
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2306 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2305 uu____2306 in
                    failwith uu____2304
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2309 =
                    let uu____2310 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2310 in
                  mk uu____2309 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2317 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2317
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2319 = lookup_bvar env x in
                  (match uu____2319 with
                   | Univ uu____2320 ->
>>>>>>> taramana_pointers_with_codes_modifies
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2324) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
<<<<<<< HEAD
                  let uu____2391 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2391 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____2425 =
                         let uu____2426 =
                           let uu____2443 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____2443)  in
                         FStar_Syntax_Syntax.Tm_abs uu____2426  in
                       mk uu____2425 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2474 = closures_as_binders_delayed cfg env bs  in
                  (match uu____2474 with
=======
                  let uu____2412 = closures_as_binders_delayed cfg env bs in
                  (match uu____2412 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2446 =
                         let uu____2447 =
                           let uu____2464 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2464) in
                         FStar_Syntax_Syntax.Tm_abs uu____2447 in
                       mk uu____2446 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2495 = closures_as_binders_delayed cfg env bs in
                  (match uu____2495 with
>>>>>>> taramana_pointers_with_codes_modifies
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
<<<<<<< HEAD
                  let uu____2522 =
                    let uu____2535 =
                      let uu____2542 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____2542]  in
                    closures_as_binders_delayed cfg env uu____2535  in
                  (match uu____2522 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____2564 =
                         let uu____2565 =
                           let uu____2572 =
                             let uu____2573 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____2573
                               FStar_Pervasives_Native.fst
                              in
                           (uu____2572, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____2565  in
                       mk uu____2564 t1.FStar_Syntax_Syntax.pos)
=======
                  let uu____2543 =
                    let uu____2556 =
                      let uu____2563 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2563] in
                    closures_as_binders_delayed cfg env uu____2556 in
                  (match uu____2543 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2585 =
                         let uu____2586 =
                           let uu____2593 =
                             let uu____2594 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2594
                               FStar_Pervasives_Native.fst in
                           (uu____2593, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2586 in
                       mk uu____2585 t1.FStar_Syntax_Syntax.pos)
>>>>>>> taramana_pointers_with_codes_modifies
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
<<<<<<< HEAD
                        let uu____2664 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____2664
                    | FStar_Util.Inr c ->
                        let uu____2678 = close_comp cfg env c  in
                        FStar_Util.Inr uu____2678
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____2694 =
                    let uu____2695 =
                      let uu____2722 = closure_as_term_delayed cfg env t11
                         in
                      (uu____2722, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2695  in
                  mk uu____2694 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2773 =
                    let uu____2774 =
                      let uu____2781 = closure_as_term_delayed cfg env t'  in
                      let uu____2784 =
                        let uu____2785 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____2785  in
                      (uu____2781, uu____2784)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2774  in
                  mk uu____2773 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2845 =
                    let uu____2846 =
                      let uu____2853 = closure_as_term_delayed cfg env t'  in
                      let uu____2856 =
                        let uu____2857 =
                          let uu____2864 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____2864)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____2857  in
                      (uu____2853, uu____2856)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2846  in
                  mk uu____2845 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2883 =
                    let uu____2884 =
                      let uu____2891 = closure_as_term_delayed cfg env t'  in
                      let uu____2894 =
                        let uu____2895 =
                          let uu____2904 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____2904)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2895  in
                      (uu____2891, uu____2894)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2884  in
                  mk uu____2883 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2917 =
                    let uu____2918 =
                      let uu____2925 = closure_as_term_delayed cfg env t'  in
                      (uu____2925, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____2918  in
                  mk uu____2917 t1.FStar_Syntax_Syntax.pos
=======
                        let uu____2685 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2685
                    | FStar_Util.Inr c ->
                        let uu____2699 = close_comp cfg env c in
                        FStar_Util.Inr uu____2699 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2715 =
                    let uu____2716 =
                      let uu____2743 = closure_as_term_delayed cfg env t11 in
                      (uu____2743, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2716 in
                  mk uu____2715 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2794 =
                    let uu____2795 =
                      let uu____2802 = closure_as_term_delayed cfg env t' in
                      let uu____2805 =
                        let uu____2806 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2806 in
                      (uu____2802, uu____2805) in
                    FStar_Syntax_Syntax.Tm_meta uu____2795 in
                  mk uu____2794 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2866 =
                    let uu____2867 =
                      let uu____2874 = closure_as_term_delayed cfg env t' in
                      let uu____2877 =
                        let uu____2878 =
                          let uu____2885 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2885) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2878 in
                      (uu____2874, uu____2877) in
                    FStar_Syntax_Syntax.Tm_meta uu____2867 in
                  mk uu____2866 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2904 =
                    let uu____2905 =
                      let uu____2912 = closure_as_term_delayed cfg env t' in
                      let uu____2915 =
                        let uu____2916 =
                          let uu____2925 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2925) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2916 in
                      (uu____2912, uu____2915) in
                    FStar_Syntax_Syntax.Tm_meta uu____2905 in
                  mk uu____2904 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2938 =
                    let uu____2939 =
                      let uu____2946 = closure_as_term_delayed cfg env t' in
                      (uu____2946, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2939 in
                  mk uu____2938 t1.FStar_Syntax_Syntax.pos
>>>>>>> taramana_pointers_with_codes_modifies
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
<<<<<<< HEAD
                      (fun env1  -> fun uu____2955  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
=======
                      (fun env1  -> fun uu____2976  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
>>>>>>> taramana_pointers_with_codes_modifies
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
<<<<<<< HEAD
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____2962 =
                    let uu____2973 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____2973
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____2992 =
                         closure_as_term cfg (Dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___165_2998 = x  in
=======
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2983 =
                    let uu____2994 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2994
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____3013 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___165_3019 = x in
>>>>>>> taramana_pointers_with_codes_modifies
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___165_3019.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___165_3019.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
<<<<<<< HEAD
                            })), uu____2992))
                     in
                  (match uu____2962 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___166_3014 = lb  in
=======
                            })), uu____3013)) in
                  (match uu____2983 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___166_3035 = lb in
>>>>>>> taramana_pointers_with_codes_modifies
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___166_3035.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___166_3035.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3046,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
<<<<<<< HEAD
                        (fun uu____3060  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____3067 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3067
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3075  -> fun env2  -> Dummy :: env2) lbs
                          env_univs
                       in
=======
                        (fun uu____3081  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3088 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3088
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3096  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
>>>>>>> taramana_pointers_with_codes_modifies
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
<<<<<<< HEAD
                      let uu____3085 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3085
=======
                      let uu____3106 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3106
>>>>>>> taramana_pointers_with_codes_modifies
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
<<<<<<< HEAD
                           (let uu___167_3097 = x  in
=======
                           (let uu___167_3118 = x in
>>>>>>> taramana_pointers_with_codes_modifies
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___167_3118.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___167_3118.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
<<<<<<< HEAD
                            }) (fun _0_43  -> FStar_Util.Inl _0_43))
                       in
                    let uu___168_3098 = lb  in
                    let uu____3099 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
=======
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___168_3119 = lb in
                    let uu____3120 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___168_3119.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
<<<<<<< HEAD
                        (uu___168_3098.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3099
                    }  in
=======
                        (uu___168_3119.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3120
                    } in
>>>>>>> taramana_pointers_with_codes_modifies
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
<<<<<<< HEAD
                        (fun uu____3117  -> fun env1  -> Dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____3196 =
                    match uu____3196 with
=======
                        (fun uu____3138  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3217 =
                    match uu____3217 with
>>>>>>> taramana_pointers_with_codes_modifies
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3282 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3305 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3371  ->
                                        fun uu____3372  ->
                                          match (uu____3371, uu____3372) with
                                          | ((pats1,env3),(p1,b)) ->
<<<<<<< HEAD
                                              let uu____3454 =
                                                norm_pat env3 p1  in
                                              (match uu____3454 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____3284 with
                               | (pats1,env3) ->
                                   ((let uu___169_3556 = p  in
=======
                                              let uu____3475 =
                                                norm_pat env3 p1 in
                                              (match uu____3475 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3305 with
                               | (pats1,env3) ->
                                   ((let uu___169_3577 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___169_3577.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
<<<<<<< HEAD
                                let uu___170_3575 = x  in
                                let uu____3576 =
=======
                                let uu___170_3596 = x in
                                let uu____3597 =
>>>>>>> taramana_pointers_with_codes_modifies
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___170_3596.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                                    (uu___170_3575.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3576
                                }  in
                              ((let uu___171_3584 = p  in
=======
                                    (uu___170_3596.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3597
                                } in
                              ((let uu___171_3605 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___171_3605.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
<<<<<<< HEAD
                                let uu___172_3589 = x  in
                                let uu____3590 =
=======
                                let uu___172_3610 = x in
                                let uu____3611 =
>>>>>>> taramana_pointers_with_codes_modifies
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_3610.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                                    (uu___172_3589.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3590
                                }  in
                              ((let uu___173_3598 = p  in
=======
                                    (uu___172_3610.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3611
                                } in
                              ((let uu___173_3619 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___173_3619.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
<<<<<<< HEAD
                                let uu___174_3608 = x  in
                                let uu____3609 =
=======
                                let uu___174_3629 = x in
                                let uu____3630 =
>>>>>>> taramana_pointers_with_codes_modifies
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___174_3629.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                                    (uu___174_3608.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3609
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___175_3618 = p  in
=======
                                    (uu___174_3629.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3630
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___175_3639 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
<<<<<<< HEAD
                                    (uu___175_3618.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____3621 = norm_pat env1 pat  in
                        (match uu____3621 with
=======
                                    (uu___175_3639.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3642 = norm_pat env1 pat in
                        (match uu____3642 with
>>>>>>> taramana_pointers_with_codes_modifies
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
<<<<<<< HEAD
                                   let uu____3656 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____3656
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____3662 =
                    let uu____3663 =
                      let uu____3686 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____3686)  in
                    FStar_Syntax_Syntax.Tm_match uu____3663  in
                  mk uu____3662 t1.FStar_Syntax_Syntax.pos))

and closure_as_term_delayed :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
=======
                                   let uu____3677 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3677 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3683 =
                    let uu____3684 =
                      let uu____3707 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3707) in
                    FStar_Syntax_Syntax.Tm_match uu____3684 in
                  mk uu____3683 t1.FStar_Syntax_Syntax.pos))
and (closure_as_term_delayed
  :cfg ->
     closure Prims.list ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
<<<<<<< HEAD
        | uu____3768 -> closure_as_term cfg env t

and closures_as_args_delayed :
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
=======
        | uu____3789 -> closure_as_term cfg env t
and (closures_as_args_delayed
  :cfg ->
     closure Prims.list ->
       (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list ->
         (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____3813 ->
            FStar_List.map
              (fun uu____3832  ->
                 match uu____3832 with
                 | (x,imp) ->
<<<<<<< HEAD
                     let uu____3830 = closure_as_term_delayed cfg env x  in
                     (uu____3830, imp)) args

and closures_as_binders_delayed :
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,closure Prims.list)
          FStar_Pervasives_Native.tuple2
  =
=======
                     let uu____3851 = closure_as_term_delayed cfg env x in
                     (uu____3851, imp)) args
and (closures_as_binders_delayed
  :cfg ->
     closure Prims.list ->
       (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list ->
         ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list,closure Prims.list)
           FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____3867 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3922  ->
                  fun uu____3923  ->
                    match (uu____3922, uu____3923) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
<<<<<<< HEAD
                          let uu___176_3984 = b  in
                          let uu____3985 =
=======
                          let uu___176_4005 = b in
                          let uu____4006 =
>>>>>>> taramana_pointers_with_codes_modifies
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___176_4005.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                              (uu___176_3984.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3985
                          }  in
                        let env2 = Dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____3846 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and close_comp :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
=======
                              (uu___176_4005.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4006
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3867 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and (close_comp
  :cfg ->
     closure Prims.list ->
       FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____4087 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
<<<<<<< HEAD
                 let uu____4081 = closure_as_term_delayed cfg env t  in
                 let uu____4082 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4081 uu____4082
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4095 = closure_as_term_delayed cfg env t  in
                 let uu____4096 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4095 uu____4096
=======
                 let uu____4102 = closure_as_term_delayed cfg env t in
                 let uu____4103 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4102 uu____4103
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4116 = closure_as_term_delayed cfg env t in
                 let uu____4117 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4116 uu____4117
>>>>>>> taramana_pointers_with_codes_modifies
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___148_4143  ->
                           match uu___148_4143 with
                           | FStar_Syntax_Syntax.DECREASES t ->
<<<<<<< HEAD
                               let uu____4126 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____4126
                           | f -> f))
                    in
                 let uu____4130 =
                   let uu___177_4131 = c1  in
                   let uu____4132 =
=======
                               let uu____4147 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4147
                           | f -> f)) in
                 let uu____4151 =
                   let uu___177_4152 = c1 in
                   let uu____4153 =
>>>>>>> taramana_pointers_with_codes_modifies
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4153;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___177_4152.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
<<<<<<< HEAD
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4130)

and filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___149_4142  ->
            match uu___149_4142 with
            | FStar_Syntax_Syntax.DECREASES uu____4143 -> false
            | uu____4146 -> true))

and close_lcomp_opt :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
=======
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4151)
and (filter_out_lcomp_cflags
  :FStar_Syntax_Syntax.cflags Prims.list ->
     FStar_Syntax_Syntax.cflags Prims.list)=
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___149_4163  ->
            match uu___149_4163 with
            | FStar_Syntax_Syntax.DECREASES uu____4164 -> false
            | uu____4167 -> true))
and (close_lcomp_opt
  :cfg ->
     closure Prims.list ->
       FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
<<<<<<< HEAD
                   (fun uu___150_4166  ->
                      match uu___150_4166 with
                      | FStar_Syntax_Syntax.DECREASES uu____4167 -> false
                      | uu____4170 -> true))
               in
            let rc1 =
              let uu___178_4172 = rc  in
              let uu____4173 =
=======
                   (fun uu___150_4187  ->
                      match uu___150_4187 with
                      | FStar_Syntax_Syntax.DECREASES uu____4188 -> false
                      | uu____4191 -> true)) in
            let rc1 =
              let uu___178_4193 = rc in
              let uu____4194 =
>>>>>>> taramana_pointers_with_codes_modifies
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___178_4193.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4194;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
<<<<<<< HEAD
        | uu____4180 -> lopt

let built_in_primitive_steps : primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p  in
  let int_as_const p i =
    let uu____4201 =
      let uu____4202 =
        let uu____4213 = FStar_Util.string_of_int i  in
        (uu____4213, FStar_Pervasives_Native.None)  in
      FStar_Const.Const_int uu____4202  in
    const_as_tm uu____4201 p  in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p  in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p
     in
  let arg_as_int uu____4249 =
    match uu____4249 with
    | (a,uu____4257) ->
        let uu____4260 =
          let uu____4261 = FStar_Syntax_Subst.compress a  in
          uu____4261.FStar_Syntax_Syntax.n  in
        (match uu____4260 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4277 = FStar_Util.int_of_string i  in
             FStar_Pervasives_Native.Some uu____4277
         | uu____4278 -> FStar_Pervasives_Native.None)
     in
  let arg_as_bounded_int uu____4292 =
    match uu____4292 with
    | (a,uu____4304) ->
        let uu____4311 =
          let uu____4312 = FStar_Syntax_Subst.compress a  in
          uu____4312.FStar_Syntax_Syntax.n  in
        (match uu____4311 with
=======
        | uu____4201 -> lopt
let (built_in_primitive_steps :primitive_step Prims.list)=
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4222 =
      let uu____4223 =
        let uu____4234 = FStar_Util.string_of_int i in
        (uu____4234, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4223 in
    const_as_tm uu____4222 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____4270 =
    match uu____4270 with
    | (a,uu____4278) ->
        let uu____4281 =
          let uu____4282 = FStar_Syntax_Subst.compress a in
          uu____4282.FStar_Syntax_Syntax.n in
        (match uu____4281 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4298 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4298
         | uu____4299 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4313 =
    match uu____4313 with
    | (a,uu____4325) ->
        let uu____4332 =
          let uu____4333 = FStar_Syntax_Subst.compress a in
          uu____4333.FStar_Syntax_Syntax.n in
        (match uu____4332 with
>>>>>>> taramana_pointers_with_codes_modifies
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4343;
                FStar_Syntax_Syntax.vars = uu____4344;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4346;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4347;_},uu____4348)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
<<<<<<< HEAD
             let uu____4366 =
               let uu____4371 = FStar_Util.int_of_string i  in
               (fv1, uu____4371)  in
             FStar_Pervasives_Native.Some uu____4366
         | uu____4376 -> FStar_Pervasives_Native.None)
     in
  let arg_as_bool uu____4390 =
    match uu____4390 with
    | (a,uu____4398) ->
        let uu____4401 =
          let uu____4402 = FStar_Syntax_Subst.compress a  in
          uu____4402.FStar_Syntax_Syntax.n  in
        (match uu____4401 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4408 -> FStar_Pervasives_Native.None)
     in
  let arg_as_char uu____4418 =
    match uu____4418 with
    | (a,uu____4426) ->
        let uu____4429 =
          let uu____4430 = FStar_Syntax_Subst.compress a  in
          uu____4430.FStar_Syntax_Syntax.n  in
        (match uu____4429 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4436 -> FStar_Pervasives_Native.None)
     in
  let arg_as_string uu____4446 =
    match uu____4446 with
    | (a,uu____4454) ->
        let uu____4457 =
          let uu____4458 = FStar_Syntax_Subst.compress a  in
          uu____4458.FStar_Syntax_Syntax.n  in
        (match uu____4457 with
=======
             let uu____4387 =
               let uu____4392 = FStar_Util.int_of_string i in
               (fv1, uu____4392) in
             FStar_Pervasives_Native.Some uu____4387
         | uu____4397 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4411 =
    match uu____4411 with
    | (a,uu____4419) ->
        let uu____4422 =
          let uu____4423 = FStar_Syntax_Subst.compress a in
          uu____4423.FStar_Syntax_Syntax.n in
        (match uu____4422 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4429 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4439 =
    match uu____4439 with
    | (a,uu____4447) ->
        let uu____4450 =
          let uu____4451 = FStar_Syntax_Subst.compress a in
          uu____4451.FStar_Syntax_Syntax.n in
        (match uu____4450 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4457 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4467 =
    match uu____4467 with
    | (a,uu____4475) ->
        let uu____4478 =
          let uu____4479 = FStar_Syntax_Subst.compress a in
          uu____4479.FStar_Syntax_Syntax.n in
        (match uu____4478 with
>>>>>>> taramana_pointers_with_codes_modifies
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____4485)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
<<<<<<< HEAD
         | uu____4469 -> FStar_Pervasives_Native.None)
     in
  let arg_as_list f uu____4495 =
    match uu____4495 with
    | (a,uu____4509) ->
=======
         | uu____4490 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4516 =
    match uu____4516 with
    | (a,uu____4530) ->
>>>>>>> taramana_pointers_with_codes_modifies
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4559 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
<<<<<<< HEAD
              let uu____4555 = sequence xs  in
              (match uu____4555 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs'))
           in
        let uu____4575 = FStar_Syntax_Util.list_elements a  in
        (match uu____4575 with
=======
              let uu____4576 = sequence xs in
              (match uu____4576 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4596 = FStar_Syntax_Util.list_elements a in
        (match uu____4596 with
>>>>>>> taramana_pointers_with_codes_modifies
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4614 =
               FStar_List.map
                 (fun x  ->
<<<<<<< HEAD
                    let uu____4603 = FStar_Syntax_Syntax.as_arg x  in
                    f uu____4603) elts
                in
             sequence uu____4593)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4641 = f a  in FStar_Pervasives_Native.Some uu____4641
    | uu____4642 -> FStar_Pervasives_Native.None  in
=======
                    let uu____4624 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4624) elts in
             sequence uu____4614) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4662 = f a in FStar_Pervasives_Native.Some uu____4662
    | uu____4663 -> FStar_Pervasives_Native.None in
>>>>>>> taramana_pointers_with_codes_modifies
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
<<<<<<< HEAD
        let uu____4692 = f a0 a1  in FStar_Pervasives_Native.Some uu____4692
    | uu____4693 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f r args =
    let uu____4742 = FStar_List.map as_a args  in lift_unary (f r) uu____4742
     in
  let binary_op as_a f r args =
    let uu____4798 = FStar_List.map as_a args  in
    lift_binary (f r) uu____4798  in
  let as_primitive_step uu____4822 =
    match uu____4822 with
=======
        let uu____4713 = f a0 a1 in FStar_Pervasives_Native.Some uu____4713
    | uu____4714 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4763 = FStar_List.map as_a args in lift_unary (f r) uu____4763 in
  let binary_op as_a f r args =
    let uu____4819 = FStar_List.map as_a args in lift_binary (f r) uu____4819 in
  let as_primitive_step uu____4843 =
    match uu____4843 with
>>>>>>> taramana_pointers_with_codes_modifies
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f }
     in
  let unary_int_op f =
    unary_op arg_as_int
<<<<<<< HEAD
      (fun r  -> fun x  -> let uu____4870 = f x  in int_as_const r uu____4870)
     in
=======
      (fun r  -> fun x  -> let uu____4891 = f x in int_as_const r uu____4891) in
>>>>>>> taramana_pointers_with_codes_modifies
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
<<<<<<< HEAD
           fun y  -> let uu____4898 = f x y  in int_as_const r uu____4898)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  -> let uu____4919 = f x  in bool_as_const r uu____4919)
     in
=======
           fun y  -> let uu____4919 = f x y in int_as_const r uu____4919) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4940 = f x in bool_as_const r uu____4940) in
>>>>>>> taramana_pointers_with_codes_modifies
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
<<<<<<< HEAD
           fun y  -> let uu____4947 = f x y  in bool_as_const r uu____4947)
     in
=======
           fun y  -> let uu____4968 = f x y in bool_as_const r uu____4968) in
>>>>>>> taramana_pointers_with_codes_modifies
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
<<<<<<< HEAD
           fun y  -> let uu____4975 = f x y  in string_as_const r uu____4975)
     in
=======
           fun y  -> let uu____4996 = f x y in string_as_const r uu____4996) in
>>>>>>> taramana_pointers_with_codes_modifies
  let list_of_string' rng s =
    let name l =
      let uu____5010 =
        let uu____5011 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
<<<<<<< HEAD
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____4990  in
      mk uu____4989 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5000 =
      let uu____5003 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5003  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5000  in
=======
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5011 in
      mk uu____5010 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5021 =
      let uu____5024 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5024 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5021 in
>>>>>>> taramana_pointers_with_codes_modifies
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in int_as_const rng r  in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
<<<<<<< HEAD
        let uu____5078 = arg_as_string a1  in
        (match uu____5078 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5084 = arg_as_list arg_as_string a2  in
             (match uu____5084 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5097 = string_as_const rng r  in
                  FStar_Pervasives_Native.Some uu____5097
              | uu____5098 -> FStar_Pervasives_Native.None)
         | uu____5103 -> FStar_Pervasives_Native.None)
    | uu____5106 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5120 = FStar_Util.string_of_int i  in
    string_as_const rng uu____5120  in
=======
        let uu____5099 = arg_as_string a1 in
        (match uu____5099 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5105 = arg_as_list arg_as_string a2 in
             (match uu____5105 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5118 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5118
              | uu____5119 -> FStar_Pervasives_Native.None)
         | uu____5124 -> FStar_Pervasives_Native.None)
    | uu____5127 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5141 = FStar_Util.string_of_int i in
    string_as_const rng uu____5141 in
>>>>>>> taramana_pointers_with_codes_modifies
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false")  in
  let string_of_int2 rng i =
<<<<<<< HEAD
    let uu____5136 = FStar_Util.string_of_int i  in
    string_as_const rng uu____5136  in
=======
    let uu____5157 = FStar_Util.string_of_int i in
    string_as_const rng uu____5157 in
>>>>>>> taramana_pointers_with_codes_modifies
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false")  in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
<<<<<<< HEAD
      FStar_Pervasives_Native.None r
     in
  let range_of1 uu____5166 args =
    match args with
    | uu____5178::(t,uu____5180)::[] ->
        let uu____5209 = term_of_range t.FStar_Syntax_Syntax.pos  in
        FStar_Pervasives_Native.Some uu____5209
    | uu____5214 -> FStar_Pervasives_Native.None  in
=======
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5187 args =
    match args with
    | uu____5199::(t,uu____5201)::[] ->
        let uu____5230 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5230
    | uu____5235 -> FStar_Pervasives_Native.None in
>>>>>>> taramana_pointers_with_codes_modifies
  let set_range_of1 r args =
    match args with
    | uu____5273::(t,uu____5275)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____5277;
                                     FStar_Syntax_Syntax.vars = uu____5278;_},uu____5279)::[]
        ->
        FStar_Pervasives_Native.Some
<<<<<<< HEAD
          (let uu___179_5300 = t  in
=======
          (let uu___179_5321 = t in
>>>>>>> taramana_pointers_with_codes_modifies
           {
             FStar_Syntax_Syntax.n = (uu___179_5321.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___179_5321.FStar_Syntax_Syntax.vars)
           })
<<<<<<< HEAD
    | uu____5303 -> FStar_Pervasives_Native.None  in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5384 =
          let uu____5405 = arg_as_string fn  in
          let uu____5408 = arg_as_int from_line  in
          let uu____5411 = arg_as_int from_col  in
          let uu____5414 = arg_as_int to_line  in
          let uu____5417 = arg_as_int to_col  in
          (uu____5405, uu____5408, uu____5411, uu____5414, uu____5417)  in
        (match uu____5384 with
=======
    | uu____5324 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5405 =
          let uu____5426 = arg_as_string fn in
          let uu____5429 = arg_as_int from_line in
          let uu____5432 = arg_as_int from_col in
          let uu____5435 = arg_as_int to_line in
          let uu____5438 = arg_as_int to_col in
          (uu____5426, uu____5429, uu____5432, uu____5435, uu____5438) in
        (match uu____5405 with
>>>>>>> taramana_pointers_with_codes_modifies
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
<<<<<<< HEAD
               let uu____5448 = FStar_Range.mk_pos from_l from_c  in
               let uu____5449 = FStar_Range.mk_pos to_l to_c  in
               FStar_Range.mk_range fn1 uu____5448 uu____5449  in
             let uu____5450 = term_of_range r1  in
             FStar_Pervasives_Native.Some uu____5450
         | uu____5455 -> FStar_Pervasives_Native.None)
    | uu____5476 -> FStar_Pervasives_Native.None  in
=======
               let uu____5469 = FStar_Range.mk_pos from_l from_c in
               let uu____5470 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5469 uu____5470 in
             let uu____5471 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5471
         | uu____5476 -> FStar_Pervasives_Native.None)
    | uu____5497 -> FStar_Pervasives_Native.None in
>>>>>>> taramana_pointers_with_codes_modifies
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng
       in
    match args with
<<<<<<< HEAD
    | (_typ,uu____5506)::(a1,uu____5508)::(a2,uu____5510)::[] ->
        let uu____5547 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____5547 with
=======
    | (_typ,uu____5527)::(a1,uu____5529)::(a2,uu____5531)::[] ->
        let uu____5568 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5568 with
>>>>>>> taramana_pointers_with_codes_modifies
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
<<<<<<< HEAD
         | uu____5560 -> FStar_Pervasives_Native.None)
    | uu____5561 -> failwith "Unexpected number of arguments"  in
=======
         | uu____5581 -> FStar_Pervasives_Native.None)
    | uu____5582 -> failwith "Unexpected number of arguments" in
>>>>>>> taramana_pointers_with_codes_modifies
  let basic_ops =
    let uu____5600 =
      let uu____5615 =
        let uu____5630 =
          let uu____5645 =
            let uu____5660 =
              let uu____5675 =
                let uu____5690 =
                  let uu____5705 =
                    let uu____5720 =
                      let uu____5735 =
                        let uu____5750 =
                          let uu____5765 =
                            let uu____5780 =
                              let uu____5795 =
                                let uu____5810 =
                                  let uu____5825 =
                                    let uu____5840 =
                                      let uu____5855 =
                                        let uu____5870 =
                                          let uu____5885 =
                                            let uu____5900 =
                                              let uu____5913 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
<<<<<<< HEAD
                                                  "list_of_string"]
                                                 in
                                              (uu____5892,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string'))
                                               in
                                            let uu____5899 =
                                              let uu____5914 =
                                                let uu____5927 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"]
                                                   in
                                                (uu____5927,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list'))
                                                 in
                                              let uu____5936 =
                                                let uu____5951 =
                                                  let uu____5970 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"]
                                                     in
                                                  (uu____5970,
                                                    (Prims.parse_int "2"),
                                                    string_concat')
                                                   in
                                                let uu____5983 =
                                                  let uu____6004 =
                                                    let uu____6025 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"]
                                                       in
                                                    (uu____6025,
                                                      (Prims.parse_int "2"),
                                                      range_of1)
                                                     in
                                                  let uu____6040 =
                                                    let uu____6063 =
                                                      let uu____6084 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"]
                                                         in
                                                      (uu____6084,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1)
                                                       in
                                                    let uu____6099 =
                                                      let uu____6122 =
                                                        let uu____6141 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"]
                                                           in
                                                        (uu____6141,
                                                          (Prims.parse_int "5"),
                                                          mk_range1)
                                                         in
                                                      [uu____6122]  in
                                                    uu____6063 :: uu____6099
                                                     in
                                                  uu____6004 :: uu____6040
                                                   in
                                                uu____5951 :: uu____5983  in
                                              uu____5914 :: uu____5936  in
                                            uu____5879 :: uu____5899  in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5864
                                           in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5849
                                         in
=======
                                                  "list_of_string"] in
                                              (uu____5913,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5920 =
                                              let uu____5935 =
                                                let uu____5948 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5948,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5957 =
                                                let uu____5972 =
                                                  let uu____5991 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5991,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____6004 =
                                                  let uu____6025 =
                                                    let uu____6046 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6046,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6061 =
                                                    let uu____6084 =
                                                      let uu____6105 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6105,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6120 =
                                                      let uu____6143 =
                                                        let uu____6162 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6162,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6143] in
                                                    uu____6084 :: uu____6120 in
                                                  uu____6025 :: uu____6061 in
                                                uu____5972 :: uu____6004 in
                                              uu____5935 :: uu____5957 in
                                            uu____5900 :: uu____5920 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5885 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5870 in
>>>>>>> taramana_pointers_with_codes_modifies
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
<<<<<<< HEAD
                                        :: uu____5834
                                       in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5819
                                     in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5804
                                   in
=======
                                        :: uu____5855 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5840 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5825 in
>>>>>>> taramana_pointers_with_codes_modifies
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
<<<<<<< HEAD
                                  :: uu____5789
                                 in
=======
                                  :: uu____5810 in
>>>>>>> taramana_pointers_with_codes_modifies
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
<<<<<<< HEAD
                                :: uu____5774
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5759
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5744
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5729
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5714
                       in
=======
                                :: uu____5795 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5780 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5765 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5750 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5735 in
>>>>>>> taramana_pointers_with_codes_modifies
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
<<<<<<< HEAD
                      :: uu____5699
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5684
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5669
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5654
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5639
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5624
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5609
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5594
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5579
     in
=======
                      :: uu____5720 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5705 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5690 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5675 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5660 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5645 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5630 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5615 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5600 in
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
      let c = int_as_const r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____6748 =
        let uu____6749 =
          let uu____6750 = FStar_Syntax_Syntax.as_arg c  in [uu____6750]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6749  in
      uu____6748 FStar_Pervasives_Native.None r  in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6785 =
              let uu____6798 = FStar_Parser_Const.p2l ["FStar"; m; "add"]  in
              (uu____6798, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6817  ->
                        fun uu____6818  ->
                          match (uu____6817, uu____6818) with
                          | ((int_to_t1,x),(uu____6837,y)) ->
                              int_as_bounded r int_to_t1 (x + y))))
               in
            let uu____6847 =
              let uu____6862 =
                let uu____6875 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                   in
                (uu____6875, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6894  ->
                          fun uu____6895  ->
                            match (uu____6894, uu____6895) with
                            | ((int_to_t1,x),(uu____6914,y)) ->
                                int_as_bounded r int_to_t1 (x - y))))
                 in
              let uu____6924 =
                let uu____6939 =
                  let uu____6952 = FStar_Parser_Const.p2l ["FStar"; m; "mul"]
                     in
                  (uu____6952, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6971  ->
                            fun uu____6972  ->
                              match (uu____6971, uu____6972) with
                              | ((int_to_t1,x),(uu____6991,y)) ->
                                  int_as_bounded r int_to_t1 (x * y))))
                   in
                [uu____6939]  in
              uu____6862 :: uu____6924  in
            uu____6785 :: uu____6847))
     in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
  
let equality_ops : primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7087)::(a1,uu____7089)::(a2,uu____7091)::[] ->
        let uu____7128 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7128 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___180_7134 = FStar_Syntax_Util.t_true  in
=======
      let c = int_as_const r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6769 =
        let uu____6770 =
          let uu____6771 = FStar_Syntax_Syntax.as_arg c in [uu____6771] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6770 in
      uu____6769 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6806 =
              let uu____6819 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6819, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6838  ->
                        fun uu____6839  ->
                          match (uu____6838, uu____6839) with
                          | ((int_to_t1,x),(uu____6858,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6868 =
              let uu____6883 =
                let uu____6896 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6896, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6915  ->
                          fun uu____6916  ->
                            match (uu____6915, uu____6916) with
                            | ((int_to_t1,x),(uu____6935,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6945 =
                let uu____6960 =
                  let uu____6973 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6973, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6992  ->
                            fun uu____6993  ->
                              match (uu____6992, uu____6993) with
                              | ((int_to_t1,x),(uu____7012,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6960] in
              uu____6883 :: uu____6945 in
            uu____6806 :: uu____6868)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let (equality_ops :primitive_step Prims.list)=
  let interp_prop r args =
    match args with
    | (_typ,uu____7108)::(a1,uu____7110)::(a2,uu____7112)::[] ->
        let uu____7149 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7149 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___180_7155 = FStar_Syntax_Util.t_true in
>>>>>>> taramana_pointers_with_codes_modifies
                {
                  FStar_Syntax_Syntax.n =
                    (uu___180_7155.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___180_7155.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
<<<<<<< HEAD
               (let uu___181_7138 = FStar_Syntax_Util.t_false  in
=======
               (let uu___181_7159 = FStar_Syntax_Util.t_false in
>>>>>>> taramana_pointers_with_codes_modifies
                {
                  FStar_Syntax_Syntax.n =
                    (uu___181_7159.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___181_7159.FStar_Syntax_Syntax.vars)
                })
<<<<<<< HEAD
         | uu____7139 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7141)::uu____7142::(a1,uu____7144)::(a2,uu____7146)::[] ->
        let uu____7195 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7195 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___180_7201 = FStar_Syntax_Util.t_true  in
=======
         | uu____7160 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7162)::uu____7163::(a1,uu____7165)::(a2,uu____7167)::[] ->
        let uu____7216 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7216 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___180_7222 = FStar_Syntax_Util.t_true in
>>>>>>> taramana_pointers_with_codes_modifies
                {
                  FStar_Syntax_Syntax.n =
                    (uu___180_7222.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___180_7222.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
<<<<<<< HEAD
               (let uu___181_7205 = FStar_Syntax_Util.t_false  in
=======
               (let uu___181_7226 = FStar_Syntax_Util.t_false in
>>>>>>> taramana_pointers_with_codes_modifies
                {
                  FStar_Syntax_Syntax.n =
                    (uu___181_7226.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___181_7226.FStar_Syntax_Syntax.vars)
                })
<<<<<<< HEAD
         | uu____7206 -> FStar_Pervasives_Native.None)
    | uu____7207 -> failwith "Unexpected number of arguments"  in
=======
         | uu____7227 -> FStar_Pervasives_Native.None)
    | uu____7228 -> failwith "Unexpected number of arguments" in
>>>>>>> taramana_pointers_with_codes_modifies
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      interpretation = interp_prop
<<<<<<< HEAD
    }  in
  [propositional_equality; hetero_propositional_equality] 
let reduce_primops :
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
=======
    } in
  [propositional_equality; hetero_propositional_equality]
let (reduce_primops
  :cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun tm  ->
      let uu____7241 =
        FStar_All.pipe_left Prims.op_Negation
<<<<<<< HEAD
          (FStar_List.contains Primops cfg.steps)
         in
      if uu____7220
      then tm
      else
        (let uu____7222 = FStar_Syntax_Util.head_and_args tm  in
         match uu____7222 with
         | (head1,args) ->
             let uu____7259 =
               let uu____7260 = FStar_Syntax_Util.un_uinst head1  in
               uu____7260.FStar_Syntax_Syntax.n  in
             (match uu____7259 with
=======
          (FStar_List.contains Primops cfg.steps) in
      if uu____7241
      then tm
      else
        (let uu____7243 = FStar_Syntax_Util.head_and_args tm in
         match uu____7243 with
         | (head1,args) ->
             let uu____7280 =
               let uu____7281 = FStar_Syntax_Util.un_uinst head1 in
               uu____7281.FStar_Syntax_Syntax.n in
             (match uu____7280 with
>>>>>>> taramana_pointers_with_codes_modifies
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7285 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
<<<<<<< HEAD
                      cfg.primitive_steps
                     in
                  (match uu____7264 with
=======
                      cfg.primitive_steps in
                  (match uu____7285 with
>>>>>>> taramana_pointers_with_codes_modifies
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7298 =
                            prim_step.interpretation
<<<<<<< HEAD
                              head1.FStar_Syntax_Syntax.pos args
                             in
                          match uu____7277 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7281 -> tm))
  
let reduce_equality :
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___182_7292 = cfg  in
=======
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7298 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7302 -> tm))
let (reduce_equality
  :cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___182_7313 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
         {
           steps = [Primops];
           tcenv = (uu___182_7313.tcenv);
           delta_level = (uu___182_7313.delta_level);
           primitive_steps = equality_ops
         }) tm
<<<<<<< HEAD
  
let maybe_simplify :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
=======
let (maybe_simplify
  :cfg ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun tm  ->
      let steps = cfg.steps  in
      let w t =
<<<<<<< HEAD
        let uu___183_7316 = t  in
=======
        let uu___183_7337 = t in
>>>>>>> taramana_pointers_with_codes_modifies
        {
          FStar_Syntax_Syntax.n = (uu___183_7337.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
<<<<<<< HEAD
          FStar_Syntax_Syntax.vars = (uu___183_7316.FStar_Syntax_Syntax.vars)
        }  in
=======
          FStar_Syntax_Syntax.vars = (uu___183_7337.FStar_Syntax_Syntax.vars)
        } in
>>>>>>> taramana_pointers_with_codes_modifies
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
<<<<<<< HEAD
        | uu____7333 -> FStar_Pervasives_Native.None  in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg)
         in
      let tm1 = reduce_primops cfg tm  in
      let uu____7373 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps)
         in
      if uu____7373
=======
        | uu____7354 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7394 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7394
>>>>>>> taramana_pointers_with_codes_modifies
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7397;
                     FStar_Syntax_Syntax.vars = uu____7398;_},uu____7399);
                FStar_Syntax_Syntax.pos = uu____7400;
                FStar_Syntax_Syntax.vars = uu____7401;_},args)
             ->
<<<<<<< HEAD
             let uu____7406 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid
                in
             if uu____7406
             then
               let uu____7407 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               (match uu____7407 with
                | (FStar_Pervasives_Native.Some (true ),uu____7462)::
                    (uu____7463,(arg,uu____7465))::[] -> arg
                | (uu____7530,(arg,uu____7532))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7533)::[]
=======
             let uu____7427 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7427
             then
               let uu____7428 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____7428 with
                | (FStar_Pervasives_Native.Some (true ),uu____7483)::
                    (uu____7484,(arg,uu____7486))::[] -> arg
                | (uu____7551,(arg,uu____7553))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7554)::[]
>>>>>>> taramana_pointers_with_codes_modifies
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7619)::uu____7620::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7683::(FStar_Pervasives_Native.Some (false
                               ),uu____7684)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7747 -> tm1)
             else
<<<<<<< HEAD
               (let uu____7742 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid
                   in
                if uu____7742
                then
                  let uu____7743 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____7743 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7798)::uu____7799::[]
=======
               (let uu____7763 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7763
                then
                  let uu____7764 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7764 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7819)::uu____7820::[]
>>>>>>> taramana_pointers_with_codes_modifies
                      -> w FStar_Syntax_Util.t_true
                  | uu____7883::(FStar_Pervasives_Native.Some (true
                                 ),uu____7884)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7947)::
                      (uu____7948,(arg,uu____7950))::[] -> arg
                  | (uu____8015,(arg,uu____8017))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8018)::[]
                      -> arg
                  | uu____8083 -> tm1
                else
                  (let uu____8099 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                       FStar_Parser_Const.imp_lid
                      in
                   if uu____8078
                   then
                     let uu____8079 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____8079 with
                     | uu____8134::(FStar_Pervasives_Native.Some (true
                                    ),uu____8135)::[]
=======
                       FStar_Parser_Const.imp_lid in
                   if uu____8099
                   then
                     let uu____8100 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8100 with
                     | uu____8155::(FStar_Pervasives_Native.Some (true
                                    ),uu____8156)::[]
>>>>>>> taramana_pointers_with_codes_modifies
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8219)::uu____8220::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8283)::
                         (uu____8284,(arg,uu____8286))::[] -> arg
                     | (uu____8351,(p,uu____8353))::(uu____8354,(q,uu____8356))::[]
                         ->
<<<<<<< HEAD
                         let uu____8400 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8400
=======
                         let uu____8421 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8421
>>>>>>> taramana_pointers_with_codes_modifies
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8423 -> tm1
                   else
                     (let uu____8439 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8418
                      then
                        let uu____8419 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____8419 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8474)::[]
=======
                          FStar_Parser_Const.not_lid in
                      if uu____8439
                      then
                        let uu____8440 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8440 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8495)::[]
>>>>>>> taramana_pointers_with_codes_modifies
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8534)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8573 -> tm1
                      else
                        (let uu____8589 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____8568
                         then
                           match args with
                           | (t,uu____8570)::[] ->
                               let uu____8587 =
                                 let uu____8588 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____8588.FStar_Syntax_Syntax.n  in
                               (match uu____8587 with
=======
                             FStar_Parser_Const.forall_lid in
                         if uu____8589
                         then
                           match args with
                           | (t,uu____8591)::[] ->
                               let uu____8608 =
                                 let uu____8609 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8609.FStar_Syntax_Syntax.n in
                               (match uu____8608 with
>>>>>>> taramana_pointers_with_codes_modifies
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8612::[],body,uu____8614) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
<<<<<<< HEAD
                                     | uu____8620 -> tm1)
                                | uu____8623 -> tm1)
                           | (uu____8624,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8625))::
                               (t,uu____8627)::[] ->
                               let uu____8666 =
                                 let uu____8667 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____8667.FStar_Syntax_Syntax.n  in
                               (match uu____8666 with
=======
                                     | uu____8641 -> tm1)
                                | uu____8644 -> tm1)
                           | (uu____8645,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8646))::
                               (t,uu____8648)::[] ->
                               let uu____8687 =
                                 let uu____8688 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8688.FStar_Syntax_Syntax.n in
                               (match uu____8687 with
>>>>>>> taramana_pointers_with_codes_modifies
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8691::[],body,uu____8693) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8720 -> tm1)
                                | uu____8723 -> tm1)
                           | uu____8724 -> tm1
                         else
                           (let uu____8734 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____8713
                            then
                              match args with
                              | (t,uu____8715)::[] ->
                                  let uu____8732 =
                                    let uu____8733 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____8733.FStar_Syntax_Syntax.n  in
                                  (match uu____8732 with
=======
                                FStar_Parser_Const.exists_lid in
                            if uu____8734
                            then
                              match args with
                              | (t,uu____8736)::[] ->
                                  let uu____8753 =
                                    let uu____8754 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8754.FStar_Syntax_Syntax.n in
                                  (match uu____8753 with
>>>>>>> taramana_pointers_with_codes_modifies
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8757::[],body,uu____8759) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
<<<<<<< HEAD
                                        | uu____8765 -> tm1)
                                   | uu____8768 -> tm1)
                              | (uu____8769,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8770))::
                                  (t,uu____8772)::[] ->
                                  let uu____8811 =
                                    let uu____8812 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____8812.FStar_Syntax_Syntax.n  in
                                  (match uu____8811 with
=======
                                        | uu____8786 -> tm1)
                                   | uu____8789 -> tm1)
                              | (uu____8790,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8791))::
                                  (t,uu____8793)::[] ->
                                  let uu____8832 =
                                    let uu____8833 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8833.FStar_Syntax_Syntax.n in
                                  (match uu____8832 with
>>>>>>> taramana_pointers_with_codes_modifies
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8836::[],body,uu____8838) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8865 -> tm1)
                                   | uu____8868 -> tm1)
                              | uu____8869 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8880;
                FStar_Syntax_Syntax.vars = uu____8881;_},args)
             ->
<<<<<<< HEAD
             let uu____8882 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid
                in
             if uu____8882
             then
               let uu____8883 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               (match uu____8883 with
                | (FStar_Pervasives_Native.Some (true ),uu____8938)::
                    (uu____8939,(arg,uu____8941))::[] -> arg
                | (uu____9006,(arg,uu____9008))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9009)::[]
=======
             let uu____8903 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8903
             then
               let uu____8904 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____8904 with
                | (FStar_Pervasives_Native.Some (true ),uu____8959)::
                    (uu____8960,(arg,uu____8962))::[] -> arg
                | (uu____9027,(arg,uu____9029))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9030)::[]
>>>>>>> taramana_pointers_with_codes_modifies
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9095)::uu____9096::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9159::(FStar_Pervasives_Native.Some (false
                               ),uu____9160)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9223 -> tm1)
             else
<<<<<<< HEAD
               (let uu____9218 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid
                   in
                if uu____9218
                then
                  let uu____9219 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____9219 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9274)::uu____9275::[]
=======
               (let uu____9239 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9239
                then
                  let uu____9240 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____9240 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9295)::uu____9296::[]
>>>>>>> taramana_pointers_with_codes_modifies
                      -> w FStar_Syntax_Util.t_true
                  | uu____9359::(FStar_Pervasives_Native.Some (true
                                 ),uu____9360)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9423)::
                      (uu____9424,(arg,uu____9426))::[] -> arg
                  | (uu____9491,(arg,uu____9493))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9494)::[]
                      -> arg
                  | uu____9559 -> tm1
                else
                  (let uu____9575 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                       FStar_Parser_Const.imp_lid
                      in
                   if uu____9554
                   then
                     let uu____9555 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____9555 with
                     | uu____9610::(FStar_Pervasives_Native.Some (true
                                    ),uu____9611)::[]
=======
                       FStar_Parser_Const.imp_lid in
                   if uu____9575
                   then
                     let uu____9576 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____9576 with
                     | uu____9631::(FStar_Pervasives_Native.Some (true
                                    ),uu____9632)::[]
>>>>>>> taramana_pointers_with_codes_modifies
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9695)::uu____9696::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9759)::
                         (uu____9760,(arg,uu____9762))::[] -> arg
                     | (uu____9827,(p,uu____9829))::(uu____9830,(q,uu____9832))::[]
                         ->
<<<<<<< HEAD
                         let uu____9876 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____9876
=======
                         let uu____9897 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9897
>>>>>>> taramana_pointers_with_codes_modifies
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9899 -> tm1
                   else
                     (let uu____9915 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                          FStar_Parser_Const.not_lid
                         in
                      if uu____9894
                      then
                        let uu____9895 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____9895 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9950)::[]
=======
                          FStar_Parser_Const.not_lid in
                      if uu____9915
                      then
                        let uu____9916 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9916 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9971)::[]
>>>>>>> taramana_pointers_with_codes_modifies
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10010)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10049 -> tm1
                      else
                        (let uu____10065 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____10044
                         then
                           match args with
                           | (t,uu____10046)::[] ->
                               let uu____10063 =
                                 let uu____10064 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____10064.FStar_Syntax_Syntax.n  in
                               (match uu____10063 with
=======
                             FStar_Parser_Const.forall_lid in
                         if uu____10065
                         then
                           match args with
                           | (t,uu____10067)::[] ->
                               let uu____10084 =
                                 let uu____10085 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10085.FStar_Syntax_Syntax.n in
                               (match uu____10084 with
>>>>>>> taramana_pointers_with_codes_modifies
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10088::[],body,uu____10090) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
<<<<<<< HEAD
                                     | uu____10096 -> tm1)
                                | uu____10099 -> tm1)
                           | (uu____10100,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10101))::
                               (t,uu____10103)::[] ->
                               let uu____10142 =
                                 let uu____10143 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____10143.FStar_Syntax_Syntax.n  in
                               (match uu____10142 with
=======
                                     | uu____10117 -> tm1)
                                | uu____10120 -> tm1)
                           | (uu____10121,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10122))::
                               (t,uu____10124)::[] ->
                               let uu____10163 =
                                 let uu____10164 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10164.FStar_Syntax_Syntax.n in
                               (match uu____10163 with
>>>>>>> taramana_pointers_with_codes_modifies
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10167::[],body,uu____10169) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10196 -> tm1)
                                | uu____10199 -> tm1)
                           | uu____10200 -> tm1
                         else
                           (let uu____10210 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
<<<<<<< HEAD
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____10189
                            then
                              match args with
                              | (t,uu____10191)::[] ->
                                  let uu____10208 =
                                    let uu____10209 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____10209.FStar_Syntax_Syntax.n  in
                                  (match uu____10208 with
=======
                                FStar_Parser_Const.exists_lid in
                            if uu____10210
                            then
                              match args with
                              | (t,uu____10212)::[] ->
                                  let uu____10229 =
                                    let uu____10230 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10230.FStar_Syntax_Syntax.n in
                                  (match uu____10229 with
>>>>>>> taramana_pointers_with_codes_modifies
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10233::[],body,uu____10235) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
<<<<<<< HEAD
                                        | uu____10241 -> tm1)
                                   | uu____10244 -> tm1)
                              | (uu____10245,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10246))::
                                  (t,uu____10248)::[] ->
                                  let uu____10287 =
                                    let uu____10288 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____10288.FStar_Syntax_Syntax.n  in
                                  (match uu____10287 with
=======
                                        | uu____10262 -> tm1)
                                   | uu____10265 -> tm1)
                              | (uu____10266,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10267))::
                                  (t,uu____10269)::[] ->
                                  let uu____10308 =
                                    let uu____10309 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10309.FStar_Syntax_Syntax.n in
                                  (match uu____10308 with
>>>>>>> taramana_pointers_with_codes_modifies
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10312::[],body,uu____10314) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10341 -> tm1)
                                   | uu____10344 -> tm1)
                              | uu____10345 -> tm1
                            else reduce_equality cfg tm1)))))
<<<<<<< HEAD
         | uu____10334 -> tm1)
  
let is_norm_request :
  'Auu____10341 .
    FStar_Syntax_Syntax.term -> 'Auu____10341 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10354 =
        let uu____10361 =
          let uu____10362 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10362.FStar_Syntax_Syntax.n  in
        (uu____10361, args)  in
      match uu____10354 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10368::uu____10369::[]) ->
=======
         | uu____10355 -> tm1)
let is_norm_request :
  'Auu____10362 .
    FStar_Syntax_Syntax.term -> 'Auu____10362 Prims.list -> Prims.bool=
  fun hd1  ->
    fun args  ->
      let uu____10375 =
        let uu____10382 =
          let uu____10383 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10383.FStar_Syntax_Syntax.n in
        (uu____10382, args) in
      match uu____10375 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10389::uu____10390::[]) ->
>>>>>>> taramana_pointers_with_codes_modifies
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10394::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10399::uu____10400::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
<<<<<<< HEAD
      | uu____10382 -> false
  
let get_norm_request :
  'Auu____10395 .
=======
      | uu____10403 -> false
let get_norm_request :
  'Auu____10416 .
>>>>>>> taramana_pointers_with_codes_modifies
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10416) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2=
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let unembed_step s1 =
<<<<<<< HEAD
          let uu____10437 =
            let uu____10438 = FStar_Syntax_Util.un_uinst s1  in
            uu____10438.FStar_Syntax_Syntax.n  in
          match uu____10437 with
=======
          let uu____10458 =
            let uu____10459 = FStar_Syntax_Util.un_uinst s1 in
            uu____10459.FStar_Syntax_Syntax.n in
          match uu____10458 with
>>>>>>> taramana_pointers_with_codes_modifies
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta
              -> Zeta
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota
              -> Iota
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.steps_primops
              -> Primops
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta
              -> UnfoldUntil FStar_Syntax_Syntax.Delta_constant
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.steps_delta_only
              -> UnfoldUntil FStar_Syntax_Syntax.Delta_constant
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.pos = uu____10468;
                 FStar_Syntax_Syntax.vars = uu____10469;_},(names1,uu____10471)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.steps_delta_only
              ->
              let names2 = FStar_Syntax_Embeddings.unembed_string_list names1
                 in
              let lids =
                FStar_All.pipe_right names2
                  (FStar_List.map FStar_Ident.lid_of_str)
                 in
              UnfoldOnly lids
<<<<<<< HEAD
          | uu____10489 -> failwith "Not an embedded `Prims.step`"  in
        FStar_Syntax_Embeddings.unembed_list unembed_step s  in
=======
          | uu____10510 -> failwith "Not an embedded `Prims.step`" in
        FStar_Syntax_Embeddings.unembed_list unembed_step s in
>>>>>>> taramana_pointers_with_codes_modifies
      match args with
      | uu____10517::(tm,uu____10519)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____10542)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____10557)::uu____10558::(tm,uu____10560)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
<<<<<<< HEAD
            let uu____10579 =
              let uu____10582 = full_norm steps  in parse_steps uu____10582
               in
            Beta :: uu____10579  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____10591 -> failwith "Impossible"
  
let is_reify_head : stack_elt Prims.list -> Prims.bool =
  fun uu___151_10609  ->
    match uu___151_10609 with
=======
            let uu____10600 =
              let uu____10603 = full_norm steps in parse_steps uu____10603 in
            Beta :: uu____10600 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10612 -> failwith "Impossible"
let (is_reify_head :stack_elt Prims.list -> Prims.bool)=
  fun uu___151_10630  ->
    match uu___151_10630 with
>>>>>>> taramana_pointers_with_codes_modifies
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10633;
           FStar_Syntax_Syntax.vars = uu____10634;_},uu____10635,uu____10636))::uu____10637
        -> true
<<<<<<< HEAD
    | uu____10623 -> false
  
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
    | uu____10644 -> false
let rec (norm
  :cfg ->
     env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t  in
          let firstn k l =
            if (FStar_List.length l) < k
            then (l, [])
            else FStar_Util.first_N k l  in
          log cfg
<<<<<<< HEAD
            (fun uu____10758  ->
               let uu____10759 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10760 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10761 =
                 let uu____10762 =
                   let uu____10765 = firstn (Prims.parse_int "4") stack1  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10765
                    in
                 stack_to_string uu____10762  in
=======
            (fun uu____10779  ->
               let uu____10780 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10781 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10782 =
                 let uu____10783 =
                   let uu____10786 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10786 in
                 stack_to_string uu____10783 in
>>>>>>> taramana_pointers_with_codes_modifies
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10780
                 uu____10781 uu____10782);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10809 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10834 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
<<<<<<< HEAD
               let uu____10830 =
                 let uu____10831 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos  in
                 let uu____10832 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10831 uu____10832
                  in
               failwith uu____10830
=======
               let uu____10851 =
                 let uu____10852 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10853 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10852 uu____10853 in
               failwith uu____10851
>>>>>>> taramana_pointers_with_codes_modifies
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10854 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10871 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10872 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10873;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10874;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10877;
                 FStar_Syntax_Syntax.fv_delta = uu____10878;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10879;
                 FStar_Syntax_Syntax.fv_delta = uu____10880;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10881);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args  in
               let hd2 = closure_as_term cfg env hd1  in
               let t2 =
<<<<<<< HEAD
                 let uu___184_10902 = t1  in
=======
                 let uu___184_10923 = t1 in
>>>>>>> taramana_pointers_with_codes_modifies
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___184_10923.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
<<<<<<< HEAD
                     (uu___184_10902.FStar_Syntax_Syntax.vars)
                 }  in
=======
                     (uu___184_10923.FStar_Syntax_Syntax.vars)
                 } in
>>>>>>> taramana_pointers_with_codes_modifies
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10956 =
                   FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____10935) && (is_norm_request hd1 args))
=======
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10956) && (is_norm_request hd1 args))
>>>>>>> taramana_pointers_with_codes_modifies
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
<<<<<<< HEAD
                 let uu___185_10943 = cfg  in
                 let uu____10944 =
=======
                 let uu___185_10964 = cfg in
                 let uu____10965 =
>>>>>>> taramana_pointers_with_codes_modifies
                   FStar_List.filter
                     (fun uu___152_10968  ->
                        match uu___152_10968 with
                        | UnfoldOnly uu____10969 -> false
                        | NoDeltaSteps  -> false
<<<<<<< HEAD
                        | uu____10951 -> true) cfg.steps
                    in
=======
                        | uu____10972 -> true) cfg.steps in
>>>>>>> taramana_pointers_with_codes_modifies
                 {
                   steps = uu____10965;
                   tcenv = (uu___185_10964.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
<<<<<<< HEAD
                   primitive_steps = (uu___185_10943.primitive_steps)
                 }  in
               let uu____10952 = get_norm_request (norm cfg' env []) args  in
               (match uu____10952 with
=======
                   primitive_steps = (uu___185_10964.primitive_steps)
                 } in
               let uu____10973 = get_norm_request (norm cfg' env []) args in
               (match uu____10973 with
>>>>>>> taramana_pointers_with_codes_modifies
                | (s,tm) ->
                    let delta_level =
                      let uu____10989 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
<<<<<<< HEAD
                             (fun uu___153_10973  ->
                                match uu___153_10973 with
                                | UnfoldUntil uu____10974 -> true
                                | UnfoldOnly uu____10975 -> true
                                | uu____10978 -> false))
                         in
                      if uu____10968
=======
                             (fun uu___153_10994  ->
                                match uu___153_10994 with
                                | UnfoldUntil uu____10995 -> true
                                | UnfoldOnly uu____10996 -> true
                                | uu____10999 -> false)) in
                      if uu____10989
>>>>>>> taramana_pointers_with_codes_modifies
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
<<<<<<< HEAD
                      let uu___186_10983 = cfg  in
=======
                      let uu___186_11004 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                      {
                        steps = s;
                        tcenv = (uu___186_11004.tcenv);
                        delta_level;
<<<<<<< HEAD
                        primitive_steps = (uu___186_10983.primitive_steps)
                      }  in
                    let stack' = (Debug t1) ::
                      (Steps
                         ((cfg.steps), (cfg.primitive_steps),
                           (cfg.delta_level)))
                      :: stack1  in
=======
                        primitive_steps = (uu___186_11004.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____11015 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11015
                      then
                        let uu____11018 =
                          let uu____11019 =
                            let uu____11024 = FStar_Util.now () in
                            (t1, uu____11024) in
                          Debug uu____11019 in
                        uu____11018 :: tail1
                      else tail1 in
>>>>>>> taramana_pointers_with_codes_modifies
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11026;
                  FStar_Syntax_Syntax.vars = uu____11027;_},a1::a2::rest)
               ->
<<<<<<< HEAD
               let uu____11040 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11040 with
                | (hd1,uu____11056) ->
=======
               let uu____11075 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11075 with
                | (hd1,uu____11091) ->
>>>>>>> taramana_pointers_with_codes_modifies
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
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____11156);
                  FStar_Syntax_Syntax.pos = uu____11157;
                  FStar_Syntax_Syntax.vars = uu____11158;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
<<<<<<< HEAD
               let uu____11155 = FStar_List.tl stack1  in
               norm cfg env uu____11155 (FStar_Pervasives_Native.fst a)
=======
               let uu____11190 = FStar_List.tl stack1 in
               norm cfg env uu____11190 (FStar_Pervasives_Native.fst a)
>>>>>>> taramana_pointers_with_codes_modifies
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11193;
                  FStar_Syntax_Syntax.vars = uu____11194;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
<<<<<<< HEAD
               let uu____11191 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11191 with
                | (reify_head,uu____11207) ->
=======
               let uu____11226 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11226 with
                | (reify_head,uu____11242) ->
>>>>>>> taramana_pointers_with_codes_modifies
                    let a1 =
                      let uu____11264 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
<<<<<<< HEAD
                          (FStar_Pervasives_Native.fst a)
                         in
                      FStar_Syntax_Subst.compress uu____11229  in
=======
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11264 in
>>>>>>> taramana_pointers_with_codes_modifies
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11267);
                            FStar_Syntax_Syntax.pos = uu____11268;
                            FStar_Syntax_Syntax.vars = uu____11269;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11303 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1  in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
<<<<<<< HEAD
               let u1 = norm_universe cfg env u  in
               let uu____11278 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack1 uu____11278
=======
               let u1 = norm_universe cfg env u in
               let uu____11313 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11313
>>>>>>> taramana_pointers_with_codes_modifies
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11320 =
                 FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____11285
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11288 =
                      let uu____11295 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____11295, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____11288  in
                  let stack2 = us1 :: stack1  in norm cfg env stack2 t')
=======
                   (FStar_List.contains EraseUniverses) in
               if uu____11320
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11323 =
                      let uu____11330 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11330, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11323 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
>>>>>>> taramana_pointers_with_codes_modifies
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1  in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___154_11344  ->
                         match uu___154_11344 with
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
                 let uu____11347 =
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
<<<<<<< HEAD
                           FStar_Parser_Const.false_lid))
                    in
                 if uu____11312
=======
                           FStar_Parser_Const.false_lid)) in
                 if uu____11347
>>>>>>> taramana_pointers_with_codes_modifies
                 then false
                 else
                   (let uu____11349 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
<<<<<<< HEAD
                           (fun uu___155_11321  ->
                              match uu___155_11321 with
                              | UnfoldOnly uu____11322 -> true
                              | uu____11325 -> false))
                       in
                    match uu____11314 with
=======
                           (fun uu___155_11356  ->
                              match uu___155_11356 with
                              | UnfoldOnly uu____11357 -> true
                              | uu____11360 -> false)) in
                    match uu____11349 with
>>>>>>> taramana_pointers_with_codes_modifies
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
<<<<<<< HEAD
                    | uu____11329 -> should_delta)
                  in
=======
                    | uu____11364 -> should_delta) in
>>>>>>> taramana_pointers_with_codes_modifies
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
<<<<<<< HEAD
                    let uu____11334 = FStar_Syntax_Syntax.range_of_fv f  in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____11334  in
                  let uu____11335 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  match uu____11335 with
=======
                    let uu____11369 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____11369 in
                  let uu____11370 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____11370 with
>>>>>>> taramana_pointers_with_codes_modifies
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____11383  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
<<<<<<< HEAD
                         (fun uu____11359  ->
                            let uu____11360 =
                              FStar_Syntax_Print.term_to_string t0  in
                            let uu____11361 =
                              FStar_Syntax_Print.term_to_string t2  in
=======
                         (fun uu____11394  ->
                            let uu____11395 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____11396 =
                              FStar_Syntax_Print.term_to_string t2 in
>>>>>>> taramana_pointers_with_codes_modifies
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____11395 uu____11396);
                       (let t3 =
                          let uu____11398 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
<<<<<<< HEAD
                                    FStar_Syntax_Syntax.Delta_constant))
                             in
                          if uu____11363
=======
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____11398
>>>>>>> taramana_pointers_with_codes_modifies
                          then t2
                          else
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid
                                 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                              t2
                           in
                        let n1 = FStar_List.length us  in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____11408))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env)
                                 in
                              norm cfg env1 stack2 t3
                          | uu____11431 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____11432 ->
                              let uu____11433 =
                                let uu____11434 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
<<<<<<< HEAD
                                  uu____11399
                                 in
                              failwith uu____11398
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11402 = lookup_bvar env x  in
               (match uu____11402 with
                | Univ uu____11403 ->
=======
                                  uu____11434 in
                              failwith uu____11433
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11437 = lookup_bvar env x in
               (match uu____11437 with
                | Univ uu____11438 ->
>>>>>>> taramana_pointers_with_codes_modifies
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
<<<<<<< HEAD
                      let uu____11428 = FStar_ST.op_Bang r  in
                      (match uu____11428 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11509  ->
                                 let uu____11510 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____11511 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11510
                                   uu____11511);
                            (let uu____11512 =
                               let uu____11513 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____11513.FStar_Syntax_Syntax.n  in
                             match uu____11512 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11516 ->
=======
                      let uu____11463 = FStar_ST.op_Bang r in
                      (match uu____11463 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11544  ->
                                 let uu____11545 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11546 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11545
                                   uu____11546);
                            (let uu____11547 =
                               let uu____11548 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11548.FStar_Syntax_Syntax.n in
                             match uu____11547 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11551 ->
>>>>>>> taramana_pointers_with_codes_modifies
                                 norm cfg env2 stack1 t'
                             | uu____11568 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11620)::uu____11621 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11630)::uu____11631 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11641,uu____11642))::stack_rest ->
                    (match c with
                     | Univ uu____11646 -> norm cfg (c :: env) stack_rest t1
                     | uu____11647 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11652::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
<<<<<<< HEAD
                                      (fun uu____11633  ->
                                         let uu____11634 =
                                           closure_to_string c  in
=======
                                      (fun uu____11668  ->
                                         let uu____11669 =
                                           closure_to_string c in
>>>>>>> taramana_pointers_with_codes_modifies
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11669);
                                    norm cfg (c :: env) stack_rest body)
                               | FStar_Pervasives_Native.Some rc when
                                   ((FStar_Ident.lid_equals
                                       rc.FStar_Syntax_Syntax.residual_effect
                                       FStar_Parser_Const.effect_Tot_lid)
                                      ||
                                      (FStar_Ident.lid_equals
                                         rc.FStar_Syntax_Syntax.residual_effect
                                         FStar_Parser_Const.effect_GTot_lid))
                                     ||
                                     (FStar_All.pipe_right
                                        rc.FStar_Syntax_Syntax.residual_flags
                                        (FStar_Util.for_some
                                           (fun uu___156_11674  ->
                                              match uu___156_11674 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11675 -> false)))
                                   ->
                                   (log cfg
<<<<<<< HEAD
                                      (fun uu____11644  ->
                                         let uu____11645 =
                                           closure_to_string c  in
=======
                                      (fun uu____11679  ->
                                         let uu____11680 =
                                           closure_to_string c in
>>>>>>> taramana_pointers_with_codes_modifies
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11680);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11681 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11684 ->
                                   let cfg1 =
<<<<<<< HEAD
                                     let uu___187_11653 = cfg  in
=======
                                     let uu___187_11688 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___187_11688.tcenv);
                                       delta_level =
                                         (uu___187_11688.delta_level);
                                       primitive_steps =
<<<<<<< HEAD
                                         (uu___187_11653.primitive_steps)
                                     }  in
                                   let uu____11654 =
                                     closure_as_term cfg1 env t1  in
                                   rebuild cfg1 env stack1 uu____11654)
                          | uu____11655::tl1 ->
                              (log cfg
                                 (fun uu____11674  ->
                                    let uu____11675 = closure_to_string c  in
=======
                                         (uu___187_11688.primitive_steps)
                                     } in
                                   let uu____11689 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11689)
                          | uu____11690::tl1 ->
                              (log cfg
                                 (fun uu____11709  ->
                                    let uu____11710 = closure_to_string c in
>>>>>>> taramana_pointers_with_codes_modifies
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11710);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
<<<<<<< HEAD
                      (let uu___188_11705 = cfg  in
=======
                      (let uu___188_11740 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                       {
                         steps = s;
                         tcenv = (uu___188_11740.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
<<<<<<< HEAD
                       (fun uu____11766  ->
                          let uu____11767 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11767);
=======
                       (fun uu____11801  ->
                          let uu____11802 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11802);
>>>>>>> taramana_pointers_with_codes_modifies
                     norm cfg env stack2 t1)
                | (Debug uu____11803)::uu____11804 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
<<<<<<< HEAD
                      let uu____11772 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____11772
                    else
                      (let uu____11774 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11774 with
=======
                      let uu____11811 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11811
                    else
                      (let uu____11813 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11813 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____11798  -> Dummy :: env1) env)
                              in
=======
                                     fun uu____11837  -> Dummy :: env1) env) in
>>>>>>> taramana_pointers_with_codes_modifies
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11853 =
                                     FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____11814
=======
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11853
>>>>>>> taramana_pointers_with_codes_modifies
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11863 =
                                            FStar_Syntax_Subst.subst opening
<<<<<<< HEAD
                                              t2
                                             in
                                          norm cfg env' [] uu____11824)
=======
                                              t2 in
                                          norm cfg env' [] uu____11863)
>>>>>>> taramana_pointers_with_codes_modifies
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                   (let uu___189_11829 = rc  in
=======
                                   (let uu___189_11868 = rc in
>>>>>>> taramana_pointers_with_codes_modifies
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_11868.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_11868.FStar_Syntax_Syntax.residual_flags)
                                    })
<<<<<<< HEAD
                             | uu____11830 -> lopt  in
=======
                             | uu____11869 -> lopt in
>>>>>>> taramana_pointers_with_codes_modifies
                           (log cfg
                              (fun uu____11875  ->
                                 let uu____11876 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11876);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___190_11850 = cfg  in
                               let uu____11851 =
=======
                               let uu___190_11889 = cfg in
                               let uu____11890 =
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
<<<<<<< HEAD
                                 steps = (uu___190_11850.steps);
                                 tcenv = (uu___190_11850.tcenv);
                                 delta_level = (uu___190_11850.delta_level);
                                 primitive_steps = uu____11851
                               }  in
=======
                                 steps = (uu___190_11889.steps);
                                 tcenv = (uu___190_11889.tcenv);
                                 delta_level = (uu___190_11889.delta_level);
                                 primitive_steps = uu____11890
                               } in
>>>>>>> taramana_pointers_with_codes_modifies
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11899)::uu____11900 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
<<<<<<< HEAD
                      let uu____11868 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____11868
                    else
                      (let uu____11870 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11870 with
=======
                      let uu____11907 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11907
                    else
                      (let uu____11909 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11909 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____11894  -> Dummy :: env1) env)
                              in
=======
                                     fun uu____11933  -> Dummy :: env1) env) in
>>>>>>> taramana_pointers_with_codes_modifies
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11949 =
                                     FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____11910
=======
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11949
>>>>>>> taramana_pointers_with_codes_modifies
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11959 =
                                            FStar_Syntax_Subst.subst opening
<<<<<<< HEAD
                                              t2
                                             in
                                          norm cfg env' [] uu____11920)
=======
                                              t2 in
                                          norm cfg env' [] uu____11959)
>>>>>>> taramana_pointers_with_codes_modifies
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                   (let uu___189_11925 = rc  in
=======
                                   (let uu___189_11964 = rc in
>>>>>>> taramana_pointers_with_codes_modifies
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_11964.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_11964.FStar_Syntax_Syntax.residual_flags)
                                    })
<<<<<<< HEAD
                             | uu____11926 -> lopt  in
=======
                             | uu____11965 -> lopt in
>>>>>>> taramana_pointers_with_codes_modifies
                           (log cfg
                              (fun uu____11971  ->
                                 let uu____11972 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11972);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___190_11946 = cfg  in
                               let uu____11947 =
=======
                               let uu___190_11985 = cfg in
                               let uu____11986 =
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
<<<<<<< HEAD
                                 steps = (uu___190_11946.steps);
                                 tcenv = (uu___190_11946.tcenv);
                                 delta_level = (uu___190_11946.delta_level);
                                 primitive_steps = uu____11947
                               }  in
=======
                                 steps = (uu___190_11985.steps);
                                 tcenv = (uu___190_11985.tcenv);
                                 delta_level = (uu___190_11985.delta_level);
                                 primitive_steps = uu____11986
                               } in
>>>>>>> taramana_pointers_with_codes_modifies
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11995)::uu____11996 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
<<<<<<< HEAD
                      let uu____11968 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____11968
                    else
                      (let uu____11970 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11970 with
=======
                      let uu____12007 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12007
                    else
                      (let uu____12009 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12009 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____11994  -> Dummy :: env1) env)
                              in
=======
                                     fun uu____12033  -> Dummy :: env1) env) in
>>>>>>> taramana_pointers_with_codes_modifies
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12049 =
                                     FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12010
=======
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12049
>>>>>>> taramana_pointers_with_codes_modifies
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12059 =
                                            FStar_Syntax_Subst.subst opening
<<<<<<< HEAD
                                              t2
                                             in
                                          norm cfg env' [] uu____12020)
=======
                                              t2 in
                                          norm cfg env' [] uu____12059)
>>>>>>> taramana_pointers_with_codes_modifies
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                   (let uu___189_12025 = rc  in
=======
                                   (let uu___189_12064 = rc in
>>>>>>> taramana_pointers_with_codes_modifies
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12064.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12064.FStar_Syntax_Syntax.residual_flags)
                                    })
<<<<<<< HEAD
                             | uu____12026 -> lopt  in
=======
                             | uu____12065 -> lopt in
>>>>>>> taramana_pointers_with_codes_modifies
                           (log cfg
                              (fun uu____12071  ->
                                 let uu____12072 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12072);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___190_12046 = cfg  in
                               let uu____12047 =
=======
                               let uu___190_12085 = cfg in
                               let uu____12086 =
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
<<<<<<< HEAD
                                 steps = (uu___190_12046.steps);
                                 tcenv = (uu___190_12046.tcenv);
                                 delta_level = (uu___190_12046.delta_level);
                                 primitive_steps = uu____12047
                               }  in
=======
                                 steps = (uu___190_12085.steps);
                                 tcenv = (uu___190_12085.tcenv);
                                 delta_level = (uu___190_12085.delta_level);
                                 primitive_steps = uu____12086
                               } in
>>>>>>> taramana_pointers_with_codes_modifies
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12095)::uu____12096 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
<<<<<<< HEAD
                      let uu____12066 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____12066
                    else
                      (let uu____12068 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12068 with
=======
                      let uu____12105 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12105
                    else
                      (let uu____12107 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12107 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____12092  -> Dummy :: env1) env)
                              in
=======
                                     fun uu____12131  -> Dummy :: env1) env) in
>>>>>>> taramana_pointers_with_codes_modifies
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12147 =
                                     FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12108
=======
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12147
>>>>>>> taramana_pointers_with_codes_modifies
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12157 =
                                            FStar_Syntax_Subst.subst opening
<<<<<<< HEAD
                                              t2
                                             in
                                          norm cfg env' [] uu____12118)
=======
                                              t2 in
                                          norm cfg env' [] uu____12157)
>>>>>>> taramana_pointers_with_codes_modifies
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                   (let uu___189_12123 = rc  in
=======
                                   (let uu___189_12162 = rc in
>>>>>>> taramana_pointers_with_codes_modifies
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12162.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12162.FStar_Syntax_Syntax.residual_flags)
                                    })
<<<<<<< HEAD
                             | uu____12124 -> lopt  in
=======
                             | uu____12163 -> lopt in
>>>>>>> taramana_pointers_with_codes_modifies
                           (log cfg
                              (fun uu____12169  ->
                                 let uu____12170 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12170);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___190_12144 = cfg  in
                               let uu____12145 =
=======
                               let uu___190_12183 = cfg in
                               let uu____12184 =
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
<<<<<<< HEAD
                                 steps = (uu___190_12144.steps);
                                 tcenv = (uu___190_12144.tcenv);
                                 delta_level = (uu___190_12144.delta_level);
                                 primitive_steps = uu____12145
                               }  in
=======
                                 steps = (uu___190_12183.steps);
                                 tcenv = (uu___190_12183.tcenv);
                                 delta_level = (uu___190_12183.delta_level);
                                 primitive_steps = uu____12184
                               } in
>>>>>>> taramana_pointers_with_codes_modifies
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12193)::uu____12194 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
<<<<<<< HEAD
                      let uu____12170 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____12170
                    else
                      (let uu____12172 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12172 with
=======
                      let uu____12209 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12209
                    else
                      (let uu____12211 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12211 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____12196  -> Dummy :: env1) env)
                              in
=======
                                     fun uu____12235  -> Dummy :: env1) env) in
>>>>>>> taramana_pointers_with_codes_modifies
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12251 =
                                     FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12212
=======
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12251
>>>>>>> taramana_pointers_with_codes_modifies
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12261 =
                                            FStar_Syntax_Subst.subst opening
<<<<<<< HEAD
                                              t2
                                             in
                                          norm cfg env' [] uu____12222)
=======
                                              t2 in
                                          norm cfg env' [] uu____12261)
>>>>>>> taramana_pointers_with_codes_modifies
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                   (let uu___189_12227 = rc  in
=======
                                   (let uu___189_12266 = rc in
>>>>>>> taramana_pointers_with_codes_modifies
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12266.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12266.FStar_Syntax_Syntax.residual_flags)
                                    })
<<<<<<< HEAD
                             | uu____12228 -> lopt  in
=======
                             | uu____12267 -> lopt in
>>>>>>> taramana_pointers_with_codes_modifies
                           (log cfg
                              (fun uu____12273  ->
                                 let uu____12274 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12274);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___190_12248 = cfg  in
                               let uu____12249 =
=======
                               let uu___190_12287 = cfg in
                               let uu____12288 =
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
<<<<<<< HEAD
                                 steps = (uu___190_12248.steps);
                                 tcenv = (uu___190_12248.tcenv);
                                 delta_level = (uu___190_12248.delta_level);
                                 primitive_steps = uu____12249
                               }  in
=======
                                 steps = (uu___190_12287.steps);
                                 tcenv = (uu___190_12287.tcenv);
                                 delta_level = (uu___190_12287.delta_level);
                                 primitive_steps = uu____12288
                               } in
>>>>>>> taramana_pointers_with_codes_modifies
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
<<<<<<< HEAD
                      let uu____12258 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____12258
                    else
                      (let uu____12260 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12260 with
=======
                      let uu____12297 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12297
                    else
                      (let uu____12299 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12299 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____12284  -> Dummy :: env1) env)
                              in
=======
                                     fun uu____12323  -> Dummy :: env1) env) in
>>>>>>> taramana_pointers_with_codes_modifies
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12339 =
                                     FStar_All.pipe_right cfg.steps
<<<<<<< HEAD
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12300
=======
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12339
>>>>>>> taramana_pointers_with_codes_modifies
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12349 =
                                            FStar_Syntax_Subst.subst opening
<<<<<<< HEAD
                                              t2
                                             in
                                          norm cfg env' [] uu____12310)
=======
                                              t2 in
                                          norm cfg env' [] uu____12349)
>>>>>>> taramana_pointers_with_codes_modifies
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                   (let uu___189_12315 = rc  in
=======
                                   (let uu___189_12354 = rc in
>>>>>>> taramana_pointers_with_codes_modifies
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12354.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12354.FStar_Syntax_Syntax.residual_flags)
                                    })
<<<<<<< HEAD
                             | uu____12316 -> lopt  in
=======
                             | uu____12355 -> lopt in
>>>>>>> taramana_pointers_with_codes_modifies
                           (log cfg
                              (fun uu____12361  ->
                                 let uu____12362 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12362);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___190_12336 = cfg  in
                               let uu____12337 =
=======
                               let uu___190_12375 = cfg in
                               let uu____12376 =
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
<<<<<<< HEAD
                                 steps = (uu___190_12336.steps);
                                 tcenv = (uu___190_12336.tcenv);
                                 delta_level = (uu___190_12336.delta_level);
                                 primitive_steps = uu____12337
                               }  in
=======
                                 steps = (uu___190_12375.steps);
                                 tcenv = (uu___190_12375.tcenv);
                                 delta_level = (uu___190_12375.delta_level);
                                 primitive_steps = uu____12376
                               } in
>>>>>>> taramana_pointers_with_codes_modifies
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12423  ->
                         fun stack2  ->
                           match uu____12423 with
                           | (a,aq) ->
                               let uu____12435 =
                                 let uu____12436 =
                                   let uu____12443 =
                                     let uu____12444 =
                                       let uu____12463 =
                                         FStar_Util.mk_ref
<<<<<<< HEAD
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12424, false)  in
                                     Clos uu____12405  in
                                   (uu____12404, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12397  in
                               uu____12396 :: stack2) args)
                  in
=======
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12463, false) in
                                     Clos uu____12444 in
                                   (uu____12443, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12436 in
                               uu____12435 :: stack2) args) in
>>>>>>> taramana_pointers_with_codes_modifies
               (log cfg
                  (fun uu____12515  ->
                     let uu____12516 =
                       FStar_All.pipe_left FStar_Util.string_of_int
<<<<<<< HEAD
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12477);
=======
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12516);
>>>>>>> taramana_pointers_with_codes_modifies
                norm cfg env stack2 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 (match (env, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
<<<<<<< HEAD
                             ((let uu___191_12501 = x  in
=======
                             ((let uu___191_12540 = x in
>>>>>>> taramana_pointers_with_codes_modifies
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___191_12540.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___191_12540.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack1 t2
<<<<<<< HEAD
                  | uu____12502 ->
                      let uu____12507 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____12507)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12510 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12510 with
=======
                  | uu____12541 ->
                      let uu____12546 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12546)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12549 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12549 with
>>>>>>> taramana_pointers_with_codes_modifies
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1  in
                      let t2 =
<<<<<<< HEAD
                        let uu____12535 =
                          let uu____12536 =
                            let uu____12543 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___192_12545 = x  in
=======
                        let uu____12574 =
                          let uu____12575 =
                            let uu____12582 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___192_12584 = x in
>>>>>>> taramana_pointers_with_codes_modifies
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___192_12584.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___192_12584.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
<<<<<<< HEAD
                              }), uu____12543)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12536  in
                        mk uu____12535 t1.FStar_Syntax_Syntax.pos  in
=======
                              }), uu____12582) in
                          FStar_Syntax_Syntax.Tm_refine uu____12575 in
                        mk uu____12574 t1.FStar_Syntax_Syntax.pos in
>>>>>>> taramana_pointers_with_codes_modifies
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
<<<<<<< HEAD
                 let uu____12564 = closure_as_term cfg env t1  in
                 rebuild cfg env stack1 uu____12564
               else
                 (let uu____12566 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12566 with
=======
                 let uu____12603 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12603
               else
                 (let uu____12605 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12605 with
>>>>>>> taramana_pointers_with_codes_modifies
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12613 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
<<<<<<< HEAD
                                  fun uu____12586  -> Dummy :: env1) env)
                           in
                        norm_comp cfg uu____12574 c1  in
                      let t2 =
                        let uu____12596 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12596 c2  in
=======
                                  fun uu____12625  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12613 c1 in
                      let t2 =
                        let uu____12635 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12635 c2 in
>>>>>>> taramana_pointers_with_codes_modifies
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12694)::uu____12695 -> norm cfg env stack1 t11
                | (Arg uu____12704)::uu____12705 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12714;
                       FStar_Syntax_Syntax.vars = uu____12715;_},uu____12716,uu____12717))::uu____12718
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12725)::uu____12726 ->
                    norm cfg env stack1 t11
<<<<<<< HEAD
                | uu____12696 ->
                    let t12 = norm cfg env [] t11  in
=======
                | uu____12735 ->
                    let t12 = norm cfg env [] t11 in
>>>>>>> taramana_pointers_with_codes_modifies
                    (log cfg
                       (fun uu____12739  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
<<<<<<< HEAD
                            let uu____12717 = norm cfg env [] t2  in
                            FStar_Util.Inl uu____12717
                        | FStar_Util.Inr c ->
                            let uu____12725 = norm_comp cfg env c  in
                            FStar_Util.Inr uu____12725
                         in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env [])  in
                      let uu____12731 =
                        let uu____12732 =
                          let uu____12733 =
                            let uu____12760 = FStar_Syntax_Util.unascribe t12
                               in
                            (uu____12760, (tc1, tacopt1), l)  in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12733  in
                        mk uu____12732 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack1 uu____12731)))
=======
                            let uu____12756 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12756
                        | FStar_Util.Inr c ->
                            let uu____12764 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12764 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12770 =
                        let uu____12771 =
                          let uu____12772 =
                            let uu____12799 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12799, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12772 in
                        mk uu____12771 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12770)))
>>>>>>> taramana_pointers_with_codes_modifies
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1  in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12875,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12876;
                               FStar_Syntax_Syntax.lbunivs = uu____12877;
                               FStar_Syntax_Syntax.lbtyp = uu____12878;
                               FStar_Syntax_Syntax.lbeff = uu____12879;
                               FStar_Syntax_Syntax.lbdef = uu____12880;_}::uu____12881),uu____12882)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
<<<<<<< HEAD
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12879 =
                 (let uu____12882 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____12882) &&
=======
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12918 =
                 (let uu____12921 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12921) &&
>>>>>>> taramana_pointers_with_codes_modifies
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12923 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
<<<<<<< HEAD
                                 PureSubtermsWithinComputations)
                             in
                          Prims.op_Negation uu____12884)))
                  in
               if uu____12879
               then
                 let env1 =
                   let uu____12888 =
                     let uu____12889 =
                       let uu____12908 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12908,
                         false)
                        in
                     Clos uu____12889  in
                   uu____12888 :: env  in
=======
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12923))) in
               if uu____12918
               then
                 let env1 =
                   let uu____12927 =
                     let uu____12928 =
                       let uu____12947 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12947,
                         false) in
                     Clos uu____12928 in
                   uu____12927 :: env in
>>>>>>> taramana_pointers_with_codes_modifies
                 norm cfg env1 stack1 body
               else
                 (let uu____12999 =
                    let uu____13004 =
                      let uu____13005 =
                        let uu____13006 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
<<<<<<< HEAD
                            FStar_Util.left
                           in
                        FStar_All.pipe_right uu____12967
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [uu____12966]  in
                    FStar_Syntax_Subst.open_term uu____12965 body  in
                  match uu____12960 with
=======
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13006
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13005] in
                    FStar_Syntax_Subst.open_term uu____13004 body in
                  match uu____12999 with
>>>>>>> taramana_pointers_with_codes_modifies
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let lbname =
                        let x =
<<<<<<< HEAD
                          let uu____12981 = FStar_List.hd bs  in
                          FStar_Pervasives_Native.fst uu____12981  in
                        FStar_Util.Inl
                          (let uu___193_12991 = x  in
=======
                          let uu____13020 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13020 in
                        FStar_Util.Inl
                          (let uu___193_13030 = x in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_13030.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_13030.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           })
                         in
                      let lb1 =
<<<<<<< HEAD
                        let uu___194_12993 = lb  in
                        let uu____12994 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
=======
                        let uu___194_13032 = lb in
                        let uu____13033 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
>>>>>>> taramana_pointers_with_codes_modifies
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___194_13032.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
<<<<<<< HEAD
                            (uu___194_12993.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____12994
                        }  in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13011  -> Dummy :: env1)
                             env)
                         in
=======
                            (uu___194_13032.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13033
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13050  -> Dummy :: env1)
                             env) in
>>>>>>> taramana_pointers_with_codes_modifies
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
<<<<<<< HEAD
               let uu____13034 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13034 with
=======
               let uu____13073 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13073 with
>>>>>>> taramana_pointers_with_codes_modifies
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13109 =
                               let uu___195_13110 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___195_13110.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___195_13110.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
<<<<<<< HEAD
                               }  in
                             FStar_Util.Inl uu____13070  in
                           let uu____13072 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13072 with
=======
                               } in
                             FStar_Util.Inl uu____13109 in
                           let uu____13111 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13111 with
>>>>>>> taramana_pointers_with_codes_modifies
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
<<<<<<< HEAD
                                 let uu____13092 =
                                   FStar_List.map (fun uu____13096  -> Dummy)
                                     lbs1
                                    in
                                 let uu____13097 =
                                   let uu____13100 =
                                     FStar_List.map
                                       (fun uu____13108  -> Dummy) xs1
                                      in
                                   FStar_List.append uu____13100 env  in
                                 FStar_List.append uu____13092 uu____13097
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13120 =
                                       let uu___196_13121 = rc  in
                                       let uu____13122 =
=======
                                 let uu____13131 =
                                   FStar_List.map (fun uu____13135  -> Dummy)
                                     lbs1 in
                                 let uu____13136 =
                                   let uu____13139 =
                                     FStar_List.map
                                       (fun uu____13147  -> Dummy) xs1 in
                                   FStar_List.append uu____13139 env in
                                 FStar_List.append uu____13131 uu____13136 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13159 =
                                       let uu___196_13160 = rc in
                                       let uu____13161 =
>>>>>>> taramana_pointers_with_codes_modifies
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___196_13160.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13161;
                                         FStar_Syntax_Syntax.residual_flags =
<<<<<<< HEAD
                                           (uu___196_13121.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13120
                                 | uu____13129 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___197_13133 = lb  in
=======
                                           (uu___196_13160.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13159
                                 | uu____13168 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___197_13172 = lb in
>>>>>>> taramana_pointers_with_codes_modifies
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___197_13172.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___197_13172.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
<<<<<<< HEAD
                      let uu____13137 =
                        FStar_List.map (fun uu____13141  -> Dummy) lbs2  in
                      FStar_List.append uu____13137 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13143 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13143 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___198_13159 = t1  in
=======
                      let uu____13176 =
                        FStar_List.map (fun uu____13180  -> Dummy) lbs2 in
                      FStar_List.append uu____13176 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13182 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13182 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___198_13198 = t1 in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___198_13198.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
<<<<<<< HEAD
                               (uu___198_13159.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13186 = closure_as_term cfg env t1  in
               rebuild cfg env stack1 uu____13186
=======
                               (uu___198_13198.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13225 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13225
>>>>>>> taramana_pointers_with_codes_modifies
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13244 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13295  ->
                        match uu____13295 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13368 =
                                let uu___199_13369 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___199_13369.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
<<<<<<< HEAD
                                    (uu___199_13330.FStar_Syntax_Syntax.sort)
                                }  in
                              FStar_Syntax_Syntax.bv_to_tm uu____13329  in
=======
                                    (uu___199_13369.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13368 in
>>>>>>> taramana_pointers_with_codes_modifies
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
<<<<<<< HEAD
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____13205 with
                | (rec_env,memos,uu____13458) ->
                    let uu____13487 =
=======
                   (env, [], (Prims.parse_int "0")) in
               (match uu____13244 with
                | (rec_env,memos,uu____13497) ->
                    let uu____13526 =
>>>>>>> taramana_pointers_with_codes_modifies
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
                             let uu____13931 =
                               let uu____13932 =
                                 let uu____13951 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None
                                    in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
<<<<<<< HEAD
                                   uu____13912, false)
                                  in
                               Clos uu____13893  in
                             uu____13892 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
=======
                                   uu____13951, false) in
                               Clos uu____13932 in
                             uu____13931 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
>>>>>>> taramana_pointers_with_codes_modifies
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14019;
                             FStar_Syntax_Syntax.vars = uu____14020;_},uu____14021,uu____14022))::uu____14023
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
<<<<<<< HEAD
                      | uu____13991 -> false  in
=======
                      | uu____14030 -> false in
>>>>>>> taramana_pointers_with_codes_modifies
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2  in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1  in
                      let cfg1 =
                        let uu____14040 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
<<<<<<< HEAD
                               PureSubtermsWithinComputations)
                           in
                        if uu____14001
                        then
                          let uu___200_14002 = cfg  in
=======
                               PureSubtermsWithinComputations) in
                        if uu____14040
                        then
                          let uu___200_14041 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___200_14041.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___200_14041.primitive_steps)
                          }
                        else
<<<<<<< HEAD
                          (let uu___201_14004 = cfg  in
=======
                          (let uu___201_14043 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___201_14043.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
<<<<<<< HEAD
                               (uu___201_14004.primitive_steps)
                           })
                         in
=======
                               (uu___201_14043.primitive_steps)
                           }) in
>>>>>>> taramana_pointers_with_codes_modifies
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
<<<<<<< HEAD
                      (let uu____14006 =
                         let uu____14007 = FStar_Syntax_Subst.compress head1
                            in
                         uu____14007.FStar_Syntax_Syntax.n  in
                       match uu____14006 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____14025 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____14025 with
                            | (uu____14026,bind_repr) ->
=======
                      (let uu____14045 =
                         let uu____14046 = FStar_Syntax_Subst.compress head1 in
                         uu____14046.FStar_Syntax_Syntax.n in
                       match uu____14045 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14064 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14064 with
                            | (uu____14065,bind_repr) ->
>>>>>>> taramana_pointers_with_codes_modifies
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14071 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
<<<<<<< HEAD
                                       let uu____14040 =
                                         let uu____14041 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____14041.FStar_Syntax_Syntax.n
                                          in
                                       match uu____14040 with
=======
                                       let uu____14079 =
                                         let uu____14080 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14080.FStar_Syntax_Syntax.n in
                                       match uu____14079 with
>>>>>>> taramana_pointers_with_codes_modifies
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14086,uu____14087))
                                           ->
<<<<<<< HEAD
                                           let uu____14057 =
                                             let uu____14058 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____14058.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____14057 with
=======
                                           let uu____14096 =
                                             let uu____14097 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14097.FStar_Syntax_Syntax.n in
                                           (match uu____14096 with
>>>>>>> taramana_pointers_with_codes_modifies
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14103,msrc,uu____14105))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14114 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14114
                                            | uu____14115 ->
                                                FStar_Pervasives_Native.None)
<<<<<<< HEAD
                                       | uu____14077 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____14078 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____14078 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___202_14083 = lb  in
=======
                                       | uu____14116 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14117 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14117 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___202_14122 = lb in
>>>>>>> taramana_pointers_with_codes_modifies
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___202_14122.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___202_14122.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___202_14122.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
<<<<<<< HEAD
                                            }  in
                                          let uu____14084 =
                                            FStar_List.tl stack1  in
                                          let uu____14085 =
                                            let uu____14086 =
                                              let uu____14089 =
                                                let uu____14090 =
                                                  let uu____14103 =
=======
                                            } in
                                          let uu____14123 =
                                            FStar_List.tl stack1 in
                                          let uu____14124 =
                                            let uu____14125 =
                                              let uu____14128 =
                                                let uu____14129 =
                                                  let uu____14142 =
>>>>>>> taramana_pointers_with_codes_modifies
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
<<<<<<< HEAD
                                                    uu____14103)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14090
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14089
                                               in
                                            uu____14086
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env uu____14084
                                            uu____14085
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14119 =
                                            let uu____14120 = is_return body
                                               in
                                            match uu____14120 with
=======
                                                    uu____14142) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14129 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14128 in
                                            uu____14125
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14123
                                            uu____14124
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14158 =
                                            let uu____14159 = is_return body in
                                            match uu____14159 with
>>>>>>> taramana_pointers_with_codes_modifies
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14163;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14164;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
<<<<<<< HEAD
                                            | uu____14130 -> false  in
                                          if uu____14119
=======
                                            | uu____14169 -> false in
                                          if uu____14158
>>>>>>> taramana_pointers_with_codes_modifies
                                          then
                                            norm cfg env stack1
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
                                               let uu____14193 =
                                                 let uu____14196 =
                                                   let uu____14197 =
                                                     let uu____14214 =
                                                       let uu____14217 =
                                                         FStar_Syntax_Syntax.mk_binder
<<<<<<< HEAD
                                                           x
                                                          in
                                                       [uu____14178]  in
                                                     (uu____14175, body1,
=======
                                                           x in
                                                       [uu____14217] in
                                                     (uu____14214, body1,
>>>>>>> taramana_pointers_with_codes_modifies
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc))
                                                      in
                                                   FStar_Syntax_Syntax.Tm_abs
<<<<<<< HEAD
                                                     uu____14158
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14157
                                                  in
                                               uu____14154
=======
                                                     uu____14197 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14196 in
                                               uu____14193
>>>>>>> taramana_pointers_with_codes_modifies
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos
                                                in
                                             let close1 =
                                               closure_as_term cfg env  in
                                             let bind_inst =
                                               let uu____14233 =
                                                 let uu____14234 =
                                                   FStar_Syntax_Subst.compress
<<<<<<< HEAD
                                                     bind_repr
                                                    in
                                                 uu____14195.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____14194 with
=======
                                                     bind_repr in
                                                 uu____14234.FStar_Syntax_Syntax.n in
                                               match uu____14233 with
>>>>>>> taramana_pointers_with_codes_modifies
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14240::uu____14241::[])
                                                   ->
                                                   let uu____14248 =
                                                     let uu____14251 =
                                                       let uu____14252 =
                                                         let uu____14259 =
                                                           let uu____14262 =
                                                             let uu____14263
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp
                                                                in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
<<<<<<< HEAD
                                                               uu____14224
                                                              in
                                                           let uu____14225 =
                                                             let uu____14228
                                                               =
                                                               let uu____14229
                                                                 = close1 t2
                                                                  in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14229
                                                                in
                                                             [uu____14228]
                                                              in
                                                           uu____14223 ::
                                                             uu____14225
                                                            in
                                                         (bind1, uu____14220)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14213
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14212
                                                      in
                                                   uu____14209
=======
                                                               uu____14263 in
                                                           let uu____14264 =
                                                             let uu____14267
                                                               =
                                                               let uu____14268
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14268 in
                                                             [uu____14267] in
                                                           uu____14262 ::
                                                             uu____14264 in
                                                         (bind1, uu____14259) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14252 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14251 in
                                                   uu____14248
>>>>>>> taramana_pointers_with_codes_modifies
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14276 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects"
                                                in
                                             let reified =
                                               let uu____14282 =
                                                 let uu____14285 =
                                                   let uu____14286 =
                                                     let uu____14301 =
                                                       let uu____14304 =
                                                         FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____14266 =
                                                         let uu____14269 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2
                                                            in
                                                         let uu____14270 =
                                                           let uu____14273 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let uu____14274 =
                                                             let uu____14277
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2
                                                                in
                                                             let uu____14278
=======
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14305 =
                                                         let uu____14308 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14309 =
                                                           let uu____14312 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14313 =
                                                             let uu____14316
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14317
>>>>>>> taramana_pointers_with_codes_modifies
                                                               =
                                                               let uu____14320
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let uu____14282
=======
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14321
>>>>>>> taramana_pointers_with_codes_modifies
                                                                 =
                                                                 let uu____14324
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                                    body2
                                                                    in
                                                                 [uu____14285]
                                                                  in
                                                               uu____14281 ::
                                                                 uu____14282
                                                                in
                                                             uu____14277 ::
                                                               uu____14278
                                                              in
                                                           uu____14273 ::
                                                             uu____14274
                                                            in
                                                         uu____14269 ::
                                                           uu____14270
                                                          in
                                                       uu____14265 ::
                                                         uu____14266
                                                        in
                                                     (bind_inst, uu____14262)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14247
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14246
                                                  in
                                               uu____14243
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____14293 =
                                               FStar_List.tl stack1  in
                                             norm cfg env uu____14293 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____14317 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____14317 with
                            | (uu____14318,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14347 =
                                        let uu____14348 =
                                          FStar_Syntax_Subst.compress t3  in
                                        uu____14348.FStar_Syntax_Syntax.n  in
                                      match uu____14347 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14354) -> t4
                                      | uu____14359 -> head2  in
                                    let uu____14360 =
                                      let uu____14361 =
                                        FStar_Syntax_Subst.compress t4  in
                                      uu____14361.FStar_Syntax_Syntax.n  in
                                    match uu____14360 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14367 ->
                                        FStar_Pervasives_Native.None
                                     in
                                  let uu____14368 = maybe_extract_fv head2
                                     in
                                  match uu____14368 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14378 =
                                        FStar_Syntax_Syntax.lid_of_fv x  in
=======
                                                                    body2 in
                                                                 [uu____14324] in
                                                               uu____14320 ::
                                                                 uu____14321 in
                                                             uu____14316 ::
                                                               uu____14317 in
                                                           uu____14312 ::
                                                             uu____14313 in
                                                         uu____14308 ::
                                                           uu____14309 in
                                                       uu____14304 ::
                                                         uu____14305 in
                                                     (bind_inst, uu____14301) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14286 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14285 in
                                               uu____14282
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14332 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14332 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14356 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14356 with
                            | (uu____14357,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14386 =
                                        let uu____14387 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14387.FStar_Syntax_Syntax.n in
                                      match uu____14386 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14393) -> t4
                                      | uu____14398 -> head2 in
                                    let uu____14399 =
                                      let uu____14400 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14400.FStar_Syntax_Syntax.n in
                                    match uu____14399 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14406 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14407 = maybe_extract_fv head2 in
                                  match uu____14407 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14417 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
>>>>>>> taramana_pointers_with_codes_modifies
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14417
                                      ->
                                      let head3 = norm cfg env [] head2  in
                                      let action_unfolded =
<<<<<<< HEAD
                                        let uu____14383 =
                                          maybe_extract_fv head3  in
                                        match uu____14383 with
=======
                                        let uu____14422 =
                                          maybe_extract_fv head3 in
                                        match uu____14422 with
>>>>>>> taramana_pointers_with_codes_modifies
                                        | FStar_Pervasives_Native.Some
                                            uu____14427 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14428 ->
                                            FStar_Pervasives_Native.Some
                                              false
                                         in
                                      (head3, action_unfolded)
<<<<<<< HEAD
                                  | uu____14394 ->
                                      (head2, FStar_Pervasives_Native.None)
                                   in
                                ((let is_arg_impure uu____14409 =
                                    match uu____14409 with
                                    | (e,q) ->
                                        let uu____14416 =
                                          let uu____14417 =
                                            FStar_Syntax_Subst.compress e  in
                                          uu____14417.FStar_Syntax_Syntax.n
                                           in
                                        (match uu____14416 with
=======
                                  | uu____14433 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14448 =
                                    match uu____14448 with
                                    | (e,q) ->
                                        let uu____14455 =
                                          let uu____14456 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14456.FStar_Syntax_Syntax.n in
                                        (match uu____14455 with
>>>>>>> taramana_pointers_with_codes_modifies
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
<<<<<<< HEAD
                                         | uu____14432 -> false)
                                     in
                                  let uu____14433 =
                                    let uu____14434 =
                                      let uu____14441 =
                                        FStar_Syntax_Syntax.as_arg head_app
                                         in
                                      uu____14441 :: args  in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14434
                                     in
                                  if uu____14433
=======
                                         | uu____14471 -> false) in
                                  let uu____14472 =
                                    let uu____14473 =
                                      let uu____14480 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14480 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14473 in
                                  if uu____14472
>>>>>>> taramana_pointers_with_codes_modifies
                                  then
                                    let uu____14485 =
                                      let uu____14486 =
                                        FStar_Syntax_Print.term_to_string
                                          head1
                                         in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
<<<<<<< HEAD
                                        uu____14447
                                       in
                                    failwith uu____14446
                                  else ());
                                 (let uu____14449 =
                                    maybe_unfold_action head_app  in
                                  match uu____14449 with
=======
                                        uu____14486 in
                                    failwith uu____14485
                                  else ());
                                 (let uu____14488 =
                                    maybe_unfold_action head_app in
                                  match uu____14488 with
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                                            ) -> body
                                         in
                                      let uu____14488 = FStar_List.tl stack1
                                         in
                                      norm cfg env uu____14488 body1)))
=======
                                            ) -> body in
                                      let uu____14527 = FStar_List.tl stack1 in
                                      norm cfg env uu____14527 body1)))
>>>>>>> taramana_pointers_with_codes_modifies
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
<<<<<<< HEAD
                             let uu____14502 = closure_as_term cfg env t'  in
                             reify_lift cfg.tcenv e msrc mtgt uu____14502  in
                           let uu____14503 = FStar_List.tl stack1  in
                           norm cfg env uu____14503 lifted
=======
                             let uu____14541 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14541 in
                           let uu____14542 = FStar_List.tl stack1 in
                           norm cfg env uu____14542 lifted
>>>>>>> taramana_pointers_with_codes_modifies
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14663  ->
                                     match uu____14663 with
                                     | (pat,wopt,tm) ->
<<<<<<< HEAD
                                         let uu____14672 =
                                           FStar_Syntax_Util.mk_reify tm  in
                                         (pat, wopt, uu____14672)))
                              in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____14704 = FStar_List.tl stack1  in
                           norm cfg env uu____14704 tm
                       | uu____14705 -> norm cfg env stack1 head1)
=======
                                         let uu____14711 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14711))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14743 = FStar_List.tl stack1 in
                           norm cfg env uu____14743 tm
                       | uu____14744 -> norm cfg env stack1 head1)
>>>>>>> taramana_pointers_with_codes_modifies
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14753;
                             FStar_Syntax_Syntax.vars = uu____14754;_},uu____14755,uu____14756))::uu____14757
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
<<<<<<< HEAD
                      | uu____14725 -> false  in
                    if should_reify
                    then
                      let uu____14726 = FStar_List.tl stack1  in
                      let uu____14727 =
                        let uu____14728 = closure_as_term cfg env t2  in
                        reify_lift cfg.tcenv head1 m1 m' uu____14728  in
                      norm cfg env uu____14726 uu____14727
                    else
                      (let t3 = norm cfg env [] t2  in
                       let uu____14731 =
=======
                      | uu____14764 -> false in
                    if should_reify
                    then
                      let uu____14765 = FStar_List.tl stack1 in
                      let uu____14766 =
                        let uu____14767 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14767 in
                      norm cfg env uu____14765 uu____14766
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14770 =
>>>>>>> taramana_pointers_with_codes_modifies
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
<<<<<<< HEAD
                                 PureSubtermsWithinComputations))
                          in
                       if uu____14731
=======
                                 PureSubtermsWithinComputations)) in
                       if uu____14770
>>>>>>> taramana_pointers_with_codes_modifies
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1  in
                         let cfg1 =
<<<<<<< HEAD
                           let uu___203_14740 = cfg  in
=======
                           let uu___203_14779 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___203_14779.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
<<<<<<< HEAD
                               (uu___203_14740.primitive_steps)
                           }  in
=======
                               (uu___203_14779.primitive_steps)
                           } in
>>>>>>> taramana_pointers_with_codes_modifies
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
                | uu____14781 ->
                    (match stack1 with
                     | uu____14782::uu____14783 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14788) ->
                              norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_alien (b,s) ->
                              norm cfg env
                                ((Meta (m, (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____14813 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1  in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
<<<<<<< HEAD
                               let uu____14788 =
                                 norm_pattern_args cfg env args  in
                               FStar_Syntax_Syntax.Meta_pattern uu____14788
                           | uu____14799 -> m  in
=======
                               let uu____14827 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14827
                           | uu____14838 -> m in
>>>>>>> taramana_pointers_with_codes_modifies
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack1 t2)))
<<<<<<< HEAD

and reify_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
and (reify_lift
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       FStar_Syntax_Syntax.monad_name ->
         FStar_Syntax_Syntax.monad_name ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
<<<<<<< HEAD
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
              let uu____14811 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____14811 with
              | (uu____14812,return_repr) ->
                  let return_inst =
                    let uu____14821 =
                      let uu____14822 =
                        FStar_Syntax_Subst.compress return_repr  in
                      uu____14822.FStar_Syntax_Syntax.n  in
                    match uu____14821 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14828::[]) ->
                        let uu____14835 =
                          let uu____14838 =
                            let uu____14839 =
                              let uu____14846 =
                                let uu____14849 =
                                  env.FStar_TypeChecker_Env.universe_of env t
                                   in
                                [uu____14849]  in
                              (return_tm, uu____14846)  in
                            FStar_Syntax_Syntax.Tm_uinst uu____14839  in
                          FStar_Syntax_Syntax.mk uu____14838  in
                        uu____14835 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14857 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  let uu____14860 =
                    let uu____14863 =
                      let uu____14864 =
                        let uu____14879 =
                          let uu____14882 = FStar_Syntax_Syntax.as_arg t  in
                          let uu____14883 =
                            let uu____14886 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____14886]  in
                          uu____14882 :: uu____14883  in
                        (return_inst, uu____14879)  in
                      FStar_Syntax_Syntax.Tm_app uu____14864  in
                    FStar_Syntax_Syntax.mk uu____14863  in
                  uu____14860 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14895 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____14895 with
=======
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
              let uu____14850 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14850 with
              | (uu____14851,return_repr) ->
                  let return_inst =
                    let uu____14860 =
                      let uu____14861 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14861.FStar_Syntax_Syntax.n in
                    match uu____14860 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14867::[]) ->
                        let uu____14874 =
                          let uu____14877 =
                            let uu____14878 =
                              let uu____14885 =
                                let uu____14888 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14888] in
                              (return_tm, uu____14885) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14878 in
                          FStar_Syntax_Syntax.mk uu____14877 in
                        uu____14874 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14896 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14899 =
                    let uu____14902 =
                      let uu____14903 =
                        let uu____14918 =
                          let uu____14921 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14922 =
                            let uu____14925 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14925] in
                          uu____14921 :: uu____14922 in
                        (return_inst, uu____14918) in
                      FStar_Syntax_Syntax.Tm_app uu____14903 in
                    FStar_Syntax_Syntax.mk uu____14902 in
                  uu____14899 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14934 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14934 with
>>>>>>> taramana_pointers_with_codes_modifies
               | FStar_Pervasives_Native.None  ->
                   let uu____14937 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
<<<<<<< HEAD
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____14898
=======
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14937
>>>>>>> taramana_pointers_with_codes_modifies
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14938;
                     FStar_TypeChecker_Env.mtarget = uu____14939;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14940;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14951;
                     FStar_TypeChecker_Env.mtarget = uu____14952;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14953;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
<<<<<<< HEAD
                   let uu____14932 = FStar_Syntax_Util.mk_reify e  in
                   lift t FStar_Syntax_Syntax.tun uu____14932)

and norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
=======
                   let uu____14971 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14971)
and (norm_pattern_args
  :cfg ->
     env ->
       (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
         (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____15027  ->
                   match uu____15027 with
                   | (a,imp) ->
<<<<<<< HEAD
                       let uu____14999 = norm cfg env [] a  in
                       (uu____14999, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
=======
                       let uu____15038 = norm cfg env [] a in
                       (uu____15038, imp))))
and (norm_comp
  :cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp  in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
<<<<<<< HEAD
            let uu___204_15016 = comp1  in
            let uu____15019 =
              let uu____15020 =
                let uu____15029 = norm cfg env [] t  in
                let uu____15030 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15029, uu____15030)  in
              FStar_Syntax_Syntax.Total uu____15020  in
=======
            let uu___204_15055 = comp1 in
            let uu____15058 =
              let uu____15059 =
                let uu____15068 = norm cfg env [] t in
                let uu____15069 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15068, uu____15069) in
              FStar_Syntax_Syntax.Total uu____15059 in
>>>>>>> taramana_pointers_with_codes_modifies
            {
              FStar_Syntax_Syntax.n = uu____15058;
              FStar_Syntax_Syntax.pos =
                (uu___204_15055.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___204_15055.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
<<<<<<< HEAD
            let uu___205_15045 = comp1  in
            let uu____15048 =
              let uu____15049 =
                let uu____15058 = norm cfg env [] t  in
                let uu____15059 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15058, uu____15059)  in
              FStar_Syntax_Syntax.GTotal uu____15049  in
=======
            let uu___205_15084 = comp1 in
            let uu____15087 =
              let uu____15088 =
                let uu____15097 = norm cfg env [] t in
                let uu____15098 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15097, uu____15098) in
              FStar_Syntax_Syntax.GTotal uu____15088 in
>>>>>>> taramana_pointers_with_codes_modifies
            {
              FStar_Syntax_Syntax.n = uu____15087;
              FStar_Syntax_Syntax.pos =
                (uu___205_15084.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___205_15084.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15150  ->
                      match uu____15150 with
                      | (a,i) ->
<<<<<<< HEAD
                          let uu____15122 = norm cfg env [] a  in
                          (uu____15122, i)))
               in
=======
                          let uu____15161 = norm cfg env [] a in
                          (uu____15161, i))) in
>>>>>>> taramana_pointers_with_codes_modifies
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___157_15172  ->
                      match uu___157_15172 with
                      | FStar_Syntax_Syntax.DECREASES t ->
<<<<<<< HEAD
                          let uu____15137 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____15137
                      | f -> f))
               in
            let uu___206_15141 = comp1  in
            let uu____15144 =
              let uu____15145 =
                let uu___207_15146 = ct  in
                let uu____15147 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____15148 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____15151 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
=======
                          let uu____15176 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15176
                      | f -> f)) in
            let uu___206_15180 = comp1 in
            let uu____15183 =
              let uu____15184 =
                let uu___207_15185 = ct in
                let uu____15186 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15187 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15190 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
>>>>>>> taramana_pointers_with_codes_modifies
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15186;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___207_15185.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15187;
                  FStar_Syntax_Syntax.effect_args = uu____15190;
                  FStar_Syntax_Syntax.flags = flags
<<<<<<< HEAD
                }  in
              FStar_Syntax_Syntax.Comp uu____15145  in
=======
                } in
              FStar_Syntax_Syntax.Comp uu____15184 in
>>>>>>> taramana_pointers_with_codes_modifies
            {
              FStar_Syntax_Syntax.n = uu____15183;
              FStar_Syntax_Syntax.pos =
                (uu___206_15180.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___206_15180.FStar_Syntax_Syntax.vars)
            }
<<<<<<< HEAD

and ghost_to_pure_aux :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
=======
and (ghost_to_pure_aux
  :cfg ->
     env ->
       FStar_Syntax_Syntax.comp ->
         FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun c  ->
        let norm1 t =
          norm
<<<<<<< HEAD
            (let uu___208_15169 = cfg  in
=======
            (let uu___208_15208 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
<<<<<<< HEAD
               tcenv = (uu___208_15169.tcenv);
               delta_level = (uu___208_15169.delta_level);
               primitive_steps = (uu___208_15169.primitive_steps)
             }) env [] t
           in
        let non_info t =
          let uu____15174 = norm1 t  in
          FStar_Syntax_Util.non_informative uu____15174  in
=======
               tcenv = (uu___208_15208.tcenv);
               delta_level = (uu___208_15208.delta_level);
               primitive_steps = (uu___208_15208.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15213 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15213 in
>>>>>>> taramana_pointers_with_codes_modifies
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15216 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
<<<<<<< HEAD
            let uu___209_15196 = c  in
=======
            let uu___209_15235 = c in
>>>>>>> taramana_pointers_with_codes_modifies
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___209_15235.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___209_15235.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
<<<<<<< HEAD
                ct.FStar_Syntax_Syntax.effect_name
               in
            let uu____15203 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ)
               in
            if uu____15203
=======
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15242 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15242
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                      else ct.FStar_Syntax_Syntax.flags  in
                    let uu___210_15214 = ct  in
=======
                      else ct.FStar_Syntax_Syntax.flags in
                    let uu___210_15253 = ct in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___210_15253.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___210_15253.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___210_15253.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
<<<<<<< HEAD
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                       in
                    let uu___211_15216 = ct1  in
=======
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___211_15255 = ct1 in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___211_15255.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___211_15255.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___211_15255.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
<<<<<<< HEAD
                        (uu___211_15216.FStar_Syntax_Syntax.flags)
                    }
                 in
              let uu___212_15217 = c  in
=======
                        (uu___211_15255.FStar_Syntax_Syntax.flags)
                    } in
              let uu___212_15256 = c in
>>>>>>> taramana_pointers_with_codes_modifies
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___212_15256.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___212_15256.FStar_Syntax_Syntax.vars)
              }
            else c
<<<<<<< HEAD
        | uu____15219 -> c

and norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
=======
        | uu____15258 -> c
and (norm_binder
  :cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun uu____15261  ->
        match uu____15261 with
        | (x,imp) ->
<<<<<<< HEAD
            let uu____15225 =
              let uu___213_15226 = x  in
              let uu____15227 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
=======
            let uu____15264 =
              let uu___213_15265 = x in
              let uu____15266 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
>>>>>>> taramana_pointers_with_codes_modifies
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___213_15265.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                  (uu___213_15226.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15227
              }  in
            (uu____15225, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
=======
                  (uu___213_15265.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15266
              } in
            (uu____15264, imp)
and (norm_binders
  :cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15272 =
          FStar_List.fold_left
            (fun uu____15290  ->
               fun b  ->
                 match uu____15290 with
                 | (nbs',env1) ->
<<<<<<< HEAD
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs
           in
        match uu____15233 with | (nbs,uu____15279) -> FStar_List.rev nbs

and norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
=======
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15272 with | (nbs,uu____15318) -> FStar_List.rev nbs
and (norm_lcomp_opt
  :cfg ->
     env ->
       FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
<<<<<<< HEAD
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____15295 =
              let uu___214_15296 = rc  in
              let uu____15297 =
=======
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____15334 =
              let uu___214_15335 = rc in
              let uu____15336 =
>>>>>>> taramana_pointers_with_codes_modifies
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___214_15335.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15336;
                FStar_Syntax_Syntax.residual_flags =
<<<<<<< HEAD
                  (uu___214_15296.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15295
        | uu____15304 -> lopt

and rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
                  (uu___214_15335.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15334
        | uu____15343 -> lopt
and (rebuild
  :cfg ->
     env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          match stack1 with
          | [] -> t
          | (Debug (tm,time_then))::stack2 ->
              ((let uu____15356 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
<<<<<<< HEAD
                    (FStar_Options.Other "print_normalized_terms")
                   in
                if uu____15316
                then
                  let uu____15317 = FStar_Syntax_Print.term_to_string tm  in
                  let uu____15318 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____15317
                    uu____15318
=======
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15356
                then
                  let time_now = FStar_Util.now () in
                  let uu____15358 =
                    let uu____15359 =
                      let uu____15360 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15360 in
                    FStar_Util.string_of_int uu____15359 in
                  let uu____15365 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15366 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15358 uu____15365 uu____15366
>>>>>>> taramana_pointers_with_codes_modifies
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
<<<<<<< HEAD
                (let uu___215_15336 = cfg  in
=======
                (let uu___215_15384 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                 {
                   steps = s;
                   tcenv = (uu___215_15384.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
<<<<<<< HEAD
                 (fun uu____15405  ->
                    let uu____15406 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15406);
=======
                 (fun uu____15453  ->
                    let uu____15454 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15454);
>>>>>>> taramana_pointers_with_codes_modifies
               rebuild cfg env stack2 t)
          | (Let (env',bs,lb,r))::stack2 ->
              let body = FStar_Syntax_Subst.close bs t  in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                  FStar_Pervasives_Native.None r
                 in
              rebuild cfg env' stack2 t1
          | (Abs (env',bs,env'',lopt,r))::stack2 ->
<<<<<<< HEAD
              let bs1 = norm_binders cfg env' bs  in
              let lopt1 = norm_lcomp_opt cfg env'' lopt  in
              let uu____15442 =
                let uu___216_15443 = FStar_Syntax_Util.abs bs1 t lopt1  in
=======
              let bs1 = norm_binders cfg env' bs in
              let lopt1 = norm_lcomp_opt cfg env'' lopt in
              let uu____15490 =
                let uu___216_15491 = FStar_Syntax_Util.abs bs1 t lopt1 in
>>>>>>> taramana_pointers_with_codes_modifies
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_15491.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
<<<<<<< HEAD
                    (uu___216_15443.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack2 uu____15442
          | (Arg (Univ uu____15444,uu____15445,uu____15446))::uu____15447 ->
=======
                    (uu___216_15491.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15490
          | (Arg (Univ uu____15492,uu____15493,uu____15494))::uu____15495 ->
>>>>>>> taramana_pointers_with_codes_modifies
              failwith "Impossible"
          | (Arg (Dummy ,uu____15498,uu____15499))::uu____15500 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15516),aq,r))::stack2 ->
              (log cfg
<<<<<<< HEAD
                 (fun uu____15497  ->
                    let uu____15498 = FStar_Syntax_Print.term_to_string tm
                       in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15498);
=======
                 (fun uu____15545  ->
                    let uu____15546 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15546);
>>>>>>> taramana_pointers_with_codes_modifies
               if FStar_List.contains (Exclude Iota) cfg.steps
               then
                 (if FStar_List.contains WHNF cfg.steps
                  then
                    let arg = closure_as_term cfg env1 tm  in
                    let t1 =
                      FStar_Syntax_Syntax.extend_app t (arg, aq)
                        FStar_Pervasives_Native.None r
                       in
                    rebuild cfg env1 stack2 t1
                  else
                    (let stack3 = (App (t, aq, r)) :: stack2  in
                     norm cfg env1 stack3 tm))
               else
<<<<<<< HEAD
                 (let uu____15508 = FStar_ST.op_Bang m  in
                  match uu____15508 with
=======
                 (let uu____15556 = FStar_ST.op_Bang m in
                  match uu____15556 with
>>>>>>> taramana_pointers_with_codes_modifies
                  | FStar_Pervasives_Native.None  ->
                      if FStar_List.contains WHNF cfg.steps
                      then
                        let arg = closure_as_term cfg env1 tm  in
                        let t1 =
                          FStar_Syntax_Syntax.extend_app t (arg, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env1 stack2 t1
                      else
                        (let stack3 = (MemoLazy m) :: (App (t, aq, r)) ::
                           stack2  in
                         norm cfg env1 stack3 tm)
                  | FStar_Pervasives_Native.Some (uu____15656,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r
                         in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
<<<<<<< HEAD
                  FStar_Pervasives_Native.None r
                 in
              let uu____15632 = maybe_simplify cfg t1  in
              rebuild cfg env stack2 uu____15632
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15642  ->
                    let uu____15643 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15643);
               (let scrutinee = t  in
                let norm_and_rebuild_match uu____15648 =
                  log cfg
                    (fun uu____15653  ->
                       let uu____15654 =
                         FStar_Syntax_Print.term_to_string scrutinee  in
                       let uu____15655 =
                         let uu____15656 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15673  ->
                                   match uu____15673 with
                                   | (p,uu____15683,uu____15684) ->
                                       FStar_Syntax_Print.pat_to_string p))
                            in
                         FStar_All.pipe_right uu____15656
                           (FStar_String.concat "\n\t")
                          in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15654 uu____15655);
                  (let whnf = FStar_List.contains WHNF cfg.steps  in
=======
                  FStar_Pervasives_Native.None r in
              let uu____15680 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15680
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15690  ->
                    let uu____15691 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15691);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15696 =
                  log cfg
                    (fun uu____15701  ->
                       let uu____15702 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15703 =
                         let uu____15704 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15721  ->
                                   match uu____15721 with
                                   | (p,uu____15731,uu____15732) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15704
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15702 uu____15703);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
>>>>>>> taramana_pointers_with_codes_modifies
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___158_15749  ->
                               match uu___158_15749 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
<<<<<<< HEAD
                               | uu____15702 -> false))
                        in
=======
                               | uu____15750 -> false)) in
>>>>>>> taramana_pointers_with_codes_modifies
                     let steps' =
                       let uu____15754 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
<<<<<<< HEAD
                              PureSubtermsWithinComputations)
                          in
                       if uu____15706
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta]  in
                     let uu___217_15710 = cfg  in
=======
                              PureSubtermsWithinComputations) in
                       if uu____15754
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___217_15758 = cfg in
>>>>>>> taramana_pointers_with_codes_modifies
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___217_15758.tcenv);
                       delta_level = new_delta;
<<<<<<< HEAD
                       primitive_steps = (uu___217_15710.primitive_steps)
                     }  in
=======
                       primitive_steps = (uu___217_15758.primitive_steps)
                     } in
>>>>>>> taramana_pointers_with_codes_modifies
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1  in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15802 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15825 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15891  ->
                                   fun uu____15892  ->
                                     match (uu____15891, uu____15892) with
                                     | ((pats1,env3),(p1,b)) ->
<<<<<<< HEAD
                                         let uu____15947 = norm_pat env3 p1
                                            in
                                         (match uu____15947 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2))
                            in
                         (match uu____15777 with
                          | (pats1,env3) ->
                              ((let uu___218_16049 = p  in
=======
                                         let uu____15995 = norm_pat env3 p1 in
                                         (match uu____15995 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15825 with
                          | (pats1,env3) ->
                              ((let uu___218_16097 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___218_16097.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
<<<<<<< HEAD
                           let uu___219_16068 = x  in
                           let uu____16069 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
=======
                           let uu___219_16116 = x in
                           let uu____16117 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___219_16116.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                               (uu___219_16068.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16069
                           }  in
                         ((let uu___220_16077 = p  in
=======
                               (uu___219_16116.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16117
                           } in
                         ((let uu___220_16125 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___220_16125.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
<<<<<<< HEAD
                           let uu___221_16082 = x  in
                           let uu____16083 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
=======
                           let uu___221_16130 = x in
                           let uu____16131 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___221_16130.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                               (uu___221_16082.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16083
                           }  in
                         ((let uu___222_16091 = p  in
=======
                               (uu___221_16130.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16131
                           } in
                         ((let uu___222_16139 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___222_16139.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
<<<<<<< HEAD
                           let uu___223_16101 = x  in
                           let uu____16102 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
=======
                           let uu___223_16149 = x in
                           let uu____16150 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___223_16149.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                               (uu___223_16101.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16102
                           }  in
                         let t2 = norm_or_whnf env2 t1  in
                         ((let uu___224_16111 = p  in
=======
                               (uu___223_16149.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16150
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___224_16159 = p in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
<<<<<<< HEAD
                               (uu___224_16111.FStar_Syntax_Syntax.p)
                           }), env2)
                      in
=======
                               (uu___224_16159.FStar_Syntax_Syntax.p)
                           }), env2) in
>>>>>>> taramana_pointers_with_codes_modifies
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____16163 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
<<<<<<< HEAD
                                 let uu____16129 =
                                   FStar_Syntax_Subst.open_branch branch1  in
                                 match uu____16129 with
                                 | (p,wopt,e) ->
                                     let uu____16149 = norm_pat env1 p  in
                                     (match uu____16149 with
=======
                                 let uu____16177 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16177 with
                                 | (p,wopt,e) ->
                                     let uu____16197 = norm_pat env1 p in
                                     (match uu____16197 with
>>>>>>> taramana_pointers_with_codes_modifies
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
<<<<<<< HEAD
                                                let uu____16180 =
                                                  norm_or_whnf env2 w  in
                                                FStar_Pervasives_Native.Some
                                                  uu____16180
                                             in
                                          let e1 = norm_or_whnf env2 e  in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1))))
                      in
                   let uu____16186 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r
                      in
                   rebuild cfg env1 stack2 uu____16186)
                   in
=======
                                                let uu____16228 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16228 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16234 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16234) in
>>>>>>> taramana_pointers_with_codes_modifies
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16244) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16249 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16250;
                        FStar_Syntax_Syntax.fv_delta = uu____16251;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16252;
                        FStar_Syntax_Syntax.fv_delta = uu____16253;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16254);_}
                      -> true
<<<<<<< HEAD
                  | uu____16213 -> false  in
=======
                  | uu____16261 -> false in
>>>>>>> taramana_pointers_with_codes_modifies
                let guard_when_clause wopt b rest =
                  match wopt with
                  | FStar_Pervasives_Native.None  -> b
                  | FStar_Pervasives_Native.Some w ->
                      let then_branch = b  in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r
                         in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch
                   in
                let rec matches_pat scrutinee_orig p =
<<<<<<< HEAD
                  let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                     in
                  let uu____16342 =
                    FStar_Syntax_Util.head_and_args scrutinee1  in
                  match uu____16342 with
=======
                  let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                  let uu____16390 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16390 with
>>>>>>> taramana_pointers_with_codes_modifies
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16439 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16442 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16445 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
<<<<<<< HEAD
                            | uu____16416 ->
                                let uu____16417 =
                                  let uu____16418 = is_cons head1  in
                                  Prims.op_Negation uu____16418  in
                                FStar_Util.Inr uu____16417)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16439 =
                             let uu____16440 =
                               FStar_Syntax_Util.un_uinst head1  in
                             uu____16440.FStar_Syntax_Syntax.n  in
                           (match uu____16439 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16450 ->
                                let uu____16451 =
                                  let uu____16452 = is_cons head1  in
                                  Prims.op_Negation uu____16452  in
                                FStar_Util.Inr uu____16451))
                
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16505)::rest_a,(p1,uu____16508)::rest_p) ->
                      let uu____16552 = matches_pat t1 p1  in
                      (match uu____16552 with
=======
                            | uu____16464 ->
                                let uu____16465 =
                                  let uu____16466 = is_cons head1 in
                                  Prims.op_Negation uu____16466 in
                                FStar_Util.Inr uu____16465)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16487 =
                             let uu____16488 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16488.FStar_Syntax_Syntax.n in
                           (match uu____16487 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16498 ->
                                let uu____16499 =
                                  let uu____16500 = is_cons head1 in
                                  Prims.op_Negation uu____16500 in
                                FStar_Util.Inr uu____16499))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16553)::rest_a,(p1,uu____16556)::rest_p) ->
                      let uu____16600 = matches_pat t1 p1 in
                      (match uu____16600 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
<<<<<<< HEAD
                  | uu____16577 -> FStar_Util.Inr false
                 in
=======
                  | uu____16625 -> FStar_Util.Inr false in
>>>>>>> taramana_pointers_with_codes_modifies
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
<<<<<<< HEAD
                      let uu____16679 = matches_pat scrutinee1 p1  in
                      (match uu____16679 with
=======
                      let uu____16727 = matches_pat scrutinee1 p1 in
                      (match uu____16727 with
>>>>>>> taramana_pointers_with_codes_modifies
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
<<<<<<< HEAD
                              (fun uu____16699  ->
                                 let uu____16700 =
                                   FStar_Syntax_Print.pat_to_string p1  in
                                 let uu____16701 =
                                   let uu____16702 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s
                                      in
                                   FStar_All.pipe_right uu____16702
                                     (FStar_String.concat "; ")
                                    in
=======
                              (fun uu____16747  ->
                                 let uu____16748 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16749 =
                                   let uu____16750 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16750
                                     (FStar_String.concat "; ") in
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16748 uu____16749);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16767 =
                                        let uu____16768 =
                                          let uu____16787 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                                 ([], t1))
                                             in
                                          ([], t1, uu____16739, false)  in
                                        Clos uu____16720  in
                                      uu____16719 :: env2) env1 s
                                in
                             let uu____16792 = guard_when_clause wopt b rest
                                in
                             norm cfg env2 stack2 uu____16792)))
                   in
                let uu____16793 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota))
                   in
                if uu____16793
                then norm_and_rebuild_match ()
                else matches scrutinee branches))

let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
=======
                                                 ([], t1)) in
                                          ([], t1, uu____16787, false) in
                                        Clos uu____16768 in
                                      uu____16767 :: env2) env1 s in
                             let uu____16840 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16840))) in
                let uu____16841 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16841
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let (config :step Prims.list -> FStar_TypeChecker_Env.env -> cfg)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___159_16864  ->
                match uu___159_16864 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
<<<<<<< HEAD
                | uu____16820 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16826 -> d  in
=======
                | uu____16868 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16874 -> d in
>>>>>>> taramana_pointers_with_codes_modifies
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps
      }
<<<<<<< HEAD
  
let normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
let (normalize_with_primitive_steps
  :primitive_step Prims.list ->
     step Prims.list ->
       FStar_TypeChecker_Env.env ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e  in
          let c1 =
<<<<<<< HEAD
            let uu___225_16855 = config s e  in
=======
            let uu___225_16903 = config s e in
>>>>>>> taramana_pointers_with_codes_modifies
            {
              steps = (uu___225_16903.steps);
              tcenv = (uu___225_16903.tcenv);
              delta_level = (uu___225_16903.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps)
            }  in
          norm c1 [] [] t
<<<<<<< HEAD
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____16880 = config s e  in norm_comp uu____16880 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16889 = config [] env  in norm_universe uu____16889 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16898 = config [] env  in ghost_to_pure_aux uu____16898 [] c
  
let ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
=======
let (normalize
  :steps ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t
let (normalize_comp
  :steps ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)=
  fun s  ->
    fun e  ->
      fun t  -> let uu____16928 = config s e in norm_comp uu____16928 [] t
let (normalize_universe
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)=
  fun env  ->
    fun u  ->
      let uu____16937 = config [] env in norm_universe uu____16937 [] u
let (ghost_to_pure
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)=
  fun env  ->
    fun c  ->
      let uu____16946 = config [] env in ghost_to_pure_aux uu____16946 [] c
let (ghost_to_pure_lcomp
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
        let uu____16912 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____16912  in
      let uu____16913 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____16913
=======
        let uu____16960 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16960 in
      let uu____16961 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16961
>>>>>>> taramana_pointers_with_codes_modifies
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
<<<<<<< HEAD
            let uu___226_16915 = lc  in
=======
            let uu___226_16963 = lc in
>>>>>>> taramana_pointers_with_codes_modifies
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___226_16963.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___226_16963.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
<<<<<<< HEAD
                ((fun uu____16918  ->
                    let uu____16919 = lc.FStar_Syntax_Syntax.comp ()  in
                    ghost_to_pure env uu____16919))
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
=======
                ((fun uu____16966  ->
                    let uu____16967 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16967))
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
let (term_to_string
  :FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
<<<<<<< HEAD
            ((let uu____16938 = FStar_Util.message_of_exn e  in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16938);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
=======
            ((let uu____16986 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16986);
             t) in
      FStar_Syntax_Print.term_to_string t1
let (comp_to_string
  :FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun c  ->
      let c1 =
        try
<<<<<<< HEAD
          let uu____16951 = config [AllowUnboundUniverses] env  in
          norm_comp uu____16951 [] c
        with
        | e ->
            ((let uu____16958 = FStar_Util.message_of_exn e  in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16958);
             c)
         in
      FStar_Syntax_Print.comp_to_string c1
  
let normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
=======
          let uu____16999 = config [AllowUnboundUniverses] env in
          norm_comp uu____16999 [] c
        with
        | e ->
            ((let uu____17006 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____17006);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let (normalize_refinement
  :steps ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                   let uu____16998 =
                     let uu____16999 =
                       let uu____17006 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____17006)  in
                     FStar_Syntax_Syntax.Tm_refine uu____16999  in
                   mk uu____16998 t01.FStar_Syntax_Syntax.pos
               | uu____17011 -> t2)
          | uu____17012 -> t2  in
        aux t
  
let unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
                   let uu____17046 =
                     let uu____17047 =
                       let uu____17054 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17054) in
                     FStar_Syntax_Syntax.Tm_refine uu____17047 in
                   mk uu____17046 t01.FStar_Syntax_Syntax.pos
               | uu____17059 -> t2)
          | uu____17060 -> t2 in
        aux t
let (unfold_whnf
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
<<<<<<< HEAD
  
let reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
let (reduce_or_remove_uvar_solutions
  :Prims.bool ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____17064 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____17064 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17093 ->
                 let uu____17100 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____17100 with
                  | (actuals,uu____17110,uu____17111) ->
=======
let (reduce_uvar_solutions
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let (remove_uvar_solutions
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let (eta_expand_with_type
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)=
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____17112 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17112 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17141 ->
                 let uu____17148 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17148 with
                  | (actuals,uu____17158,uu____17159) ->
>>>>>>> taramana_pointers_with_codes_modifies
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17173 =
                           FStar_All.pipe_right formals
<<<<<<< HEAD
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____17125 with
=======
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17173 with
>>>>>>> taramana_pointers_with_codes_modifies
                         | (binders,args) ->
                             let uu____17190 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
<<<<<<< HEAD
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____17142
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
=======
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17190
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let (eta_expand
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
<<<<<<< HEAD
      | uu____17152 ->
          let uu____17153 = FStar_Syntax_Util.head_and_args t  in
          (match uu____17153 with
           | (head1,args) ->
               let uu____17190 =
                 let uu____17191 = FStar_Syntax_Subst.compress head1  in
                 uu____17191.FStar_Syntax_Syntax.n  in
               (match uu____17190 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17194,thead) ->
                    let uu____17220 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____17220 with
=======
      | uu____17200 ->
          let uu____17201 = FStar_Syntax_Util.head_and_args t in
          (match uu____17201 with
           | (head1,args) ->
               let uu____17238 =
                 let uu____17239 = FStar_Syntax_Subst.compress head1 in
                 uu____17239.FStar_Syntax_Syntax.n in
               (match uu____17238 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17242,thead) ->
                    let uu____17268 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17268 with
>>>>>>> taramana_pointers_with_codes_modifies
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17310 =
                              env.FStar_TypeChecker_Env.type_of
<<<<<<< HEAD
                                (let uu___231_17270 = env  in
=======
                                (let uu___231_17318 = env in
>>>>>>> taramana_pointers_with_codes_modifies
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___231_17318.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___231_17318.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___231_17318.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___231_17318.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___231_17318.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___231_17318.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___231_17318.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___231_17318.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___231_17318.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___231_17318.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___231_17318.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___231_17318.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___231_17318.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___231_17318.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___231_17318.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___231_17318.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___231_17318.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___231_17318.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___231_17318.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___231_17318.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___231_17318.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___231_17318.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___231_17318.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___231_17318.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___231_17318.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
<<<<<<< HEAD
                                     (uu___231_17270.FStar_TypeChecker_Env.identifier_info)
                                 }) t
                               in
                            match uu____17262 with
                            | (uu____17271,ty,uu____17273) ->
=======
                                     (uu___231_17318.FStar_TypeChecker_Env.identifier_info)
                                 }) t in
                            match uu____17310 with
                            | (uu____17319,ty,uu____17321) ->
>>>>>>> taramana_pointers_with_codes_modifies
                                eta_expand_with_type env t ty))
                | uu____17322 ->
                    let uu____17323 =
                      env.FStar_TypeChecker_Env.type_of
<<<<<<< HEAD
                        (let uu___232_17283 = env  in
=======
                        (let uu___232_17331 = env in
>>>>>>> taramana_pointers_with_codes_modifies
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___232_17331.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___232_17331.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___232_17331.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___232_17331.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___232_17331.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___232_17331.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___232_17331.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___232_17331.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___232_17331.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___232_17331.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___232_17331.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___232_17331.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___232_17331.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___232_17331.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___232_17331.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___232_17331.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___232_17331.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___232_17331.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___232_17331.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.type_of =
                             (uu___232_17331.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___232_17331.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___232_17331.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___232_17331.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___232_17331.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___232_17331.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
<<<<<<< HEAD
                             (uu___232_17283.FStar_TypeChecker_Env.identifier_info)
                         }) t
                       in
                    (match uu____17275 with
                     | (uu____17284,ty,uu____17286) ->
                         eta_expand_with_type env t ty)))
  
let elim_uvars_aux_tc :
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
=======
                             (uu___232_17331.FStar_TypeChecker_Env.identifier_info)
                         }) t in
                    (match uu____17323 with
                     | (uu____17332,ty,uu____17334) ->
                         eta_expand_with_type env t ty)))
let (elim_uvars_aux_tc
  :FStar_TypeChecker_Env.env ->
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
             FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____17412,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
            | (uu____17370,FStar_Util.Inl t) ->
                let uu____17376 =
                  let uu____17379 =
                    let uu____17380 =
                      let uu____17393 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____17393)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____17380  in
                  FStar_Syntax_Syntax.mk uu____17379  in
                uu____17376 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____17397 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____17397 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let uu____17424 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17479 ->
                    let uu____17480 =
                      let uu____17489 =
                        let uu____17490 = FStar_Syntax_Subst.compress t3  in
                        uu____17490.FStar_Syntax_Syntax.n  in
                      (uu____17489, tc)  in
                    (match uu____17480 with
=======
            | (uu____17418,FStar_Util.Inl t) ->
                let uu____17424 =
                  let uu____17427 =
                    let uu____17428 =
                      let uu____17441 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17441) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17428 in
                  FStar_Syntax_Syntax.mk uu____17427 in
                uu____17424 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17445 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17445 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17472 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17527 ->
                    let uu____17528 =
                      let uu____17537 =
                        let uu____17538 = FStar_Syntax_Subst.compress t3 in
                        uu____17538.FStar_Syntax_Syntax.n in
                      (uu____17537, tc) in
                    (match uu____17528 with
>>>>>>> taramana_pointers_with_codes_modifies
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17563) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17600) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17639,FStar_Util.Inl uu____17640) ->
                         ([], (FStar_Util.Inl t3))
<<<<<<< HEAD
                     | uu____17615 -> failwith "Impossible")
                 in
              (match uu____17424 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
=======
                     | uu____17663 -> failwith "Impossible") in
              (match uu____17472 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let (elim_uvars_aux_t
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.univ_names ->
       FStar_Syntax_Syntax.binders ->
         FStar_Syntax_Syntax.typ ->
           (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list,FStar_Syntax_Syntax.term)
             FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
<<<<<<< HEAD
          let uu____17724 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____17724 with
          | (univ_names1,binders1,tc) ->
              let uu____17782 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____17782)
  
let elim_uvars_aux_c :
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
=======
          let uu____17772 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17772 with
          | (univ_names1,binders1,tc) ->
              let uu____17830 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17830)
let (elim_uvars_aux_c
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.univ_names ->
       FStar_Syntax_Syntax.binders ->
         FStar_Syntax_Syntax.comp ->
           (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list,FStar_Syntax_Syntax.comp'
                                                          FStar_Syntax_Syntax.syntax)
             FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
<<<<<<< HEAD
          let uu____17821 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____17821 with
          | (univ_names1,binders1,tc) ->
              let uu____17881 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____17881)
  
let rec elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
=======
          let uu____17869 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17869 with
          | (univ_names1,binders1,tc) ->
              let uu____17929 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17929)
let rec (elim_uvars
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
<<<<<<< HEAD
          let uu____17916 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____17916 with
           | (univ_names1,binders1,typ1) ->
               let uu___233_17944 = s  in
=======
          let uu____17964 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17964 with
           | (univ_names1,binders1,typ1) ->
               let uu___233_17992 = s in
>>>>>>> taramana_pointers_with_codes_modifies
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___233_17992.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___233_17992.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___233_17992.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___233_17992.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
<<<<<<< HEAD
          let uu___234_17965 = s  in
          let uu____17966 =
            let uu____17967 =
              let uu____17976 = FStar_List.map (elim_uvars env) sigs  in
              (uu____17976, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____17967  in
=======
          let uu___234_18013 = s in
          let uu____18014 =
            let uu____18015 =
              let uu____18024 = FStar_List.map (elim_uvars env) sigs in
              (uu____18024, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____18015 in
>>>>>>> taramana_pointers_with_codes_modifies
          {
            FStar_Syntax_Syntax.sigel = uu____18014;
            FStar_Syntax_Syntax.sigrng =
              (uu___234_18013.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___234_18013.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___234_18013.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___234_18013.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
<<<<<<< HEAD
          let uu____17993 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____17993 with
           | (univ_names1,uu____18011,typ1) ->
               let uu___235_18025 = s  in
=======
          let uu____18041 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18041 with
           | (univ_names1,uu____18059,typ1) ->
               let uu___235_18073 = s in
>>>>>>> taramana_pointers_with_codes_modifies
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_18073.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_18073.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_18073.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_18073.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
<<<<<<< HEAD
          let uu____18031 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____18031 with
           | (univ_names1,uu____18049,typ1) ->
               let uu___236_18063 = s  in
=======
          let uu____18079 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18079 with
           | (univ_names1,uu____18097,typ1) ->
               let uu___236_18111 = s in
>>>>>>> taramana_pointers_with_codes_modifies
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___236_18111.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___236_18111.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___236_18111.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___236_18111.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18145 =
                      FStar_Syntax_Subst.univ_var_opening
<<<<<<< HEAD
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____18097 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18120 =
                            let uu____18121 =
                              FStar_Syntax_Subst.subst opening t  in
                            remove_uvar_solutions env uu____18121  in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18120
                           in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___237_18124 = lb  in
=======
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18145 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18168 =
                            let uu____18169 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18169 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18168 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___237_18172 = lb in
>>>>>>> taramana_pointers_with_codes_modifies
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___237_18172.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___237_18172.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
<<<<<<< HEAD
                        }))
             in
          let uu___238_18125 = s  in
=======
                        })) in
          let uu___238_18173 = s in
>>>>>>> taramana_pointers_with_codes_modifies
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___238_18173.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___238_18173.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___238_18173.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___238_18173.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
<<<<<<< HEAD
          let uu___239_18137 = s  in
          let uu____18138 =
            let uu____18139 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____18139  in
=======
          let uu___239_18185 = s in
          let uu____18186 =
            let uu____18187 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18187 in
>>>>>>> taramana_pointers_with_codes_modifies
          {
            FStar_Syntax_Syntax.sigel = uu____18186;
            FStar_Syntax_Syntax.sigrng =
              (uu___239_18185.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___239_18185.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___239_18185.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___239_18185.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
<<<<<<< HEAD
          let uu____18143 = elim_uvars_aux_t env us [] t  in
          (match uu____18143 with
           | (us1,uu____18161,t1) ->
               let uu___240_18175 = s  in
=======
          let uu____18191 = elim_uvars_aux_t env us [] t in
          (match uu____18191 with
           | (us1,uu____18209,t1) ->
               let uu___240_18223 = s in
>>>>>>> taramana_pointers_with_codes_modifies
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_18223.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_18223.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_18223.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_18223.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18224 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18226 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
<<<<<<< HEAD
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____18178 with
           | (univs1,binders,signature) ->
               let uu____18206 =
                 let uu____18215 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____18215 with
                 | (univs_opening,univs2) ->
                     let uu____18242 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____18242)
                  in
               (match uu____18206 with
                | (univs_opening,univs_closing) ->
                    let uu____18259 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____18265 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____18266 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____18265, uu____18266)  in
                    (match uu____18259 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____18288 =
                           match uu____18288 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____18306 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____18306 with
=======
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18226 with
           | (univs1,binders,signature) ->
               let uu____18254 =
                 let uu____18263 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18263 with
                 | (univs_opening,univs2) ->
                     let uu____18290 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18290) in
               (match uu____18254 with
                | (univs_opening,univs_closing) ->
                    let uu____18307 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18313 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18314 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18313, uu____18314) in
                    (match uu____18307 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18336 =
                           match uu____18336 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18354 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18354 with
>>>>>>> taramana_pointers_with_codes_modifies
                                | (us1,t1) ->
                                    let uu____18365 =
                                      let uu____18370 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
<<<<<<< HEAD
                                             n_us)
                                         in
                                      let uu____18329 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____18322, uu____18329)  in
                                    (match uu____18317 with
=======
                                             n_us) in
                                      let uu____18377 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18370, uu____18377) in
                                    (match uu____18365 with
>>>>>>> taramana_pointers_with_codes_modifies
                                     | (b_opening1,b_closing1) ->
                                         let uu____18390 =
                                           let uu____18395 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
<<<<<<< HEAD
                                                  n_us)
                                              in
                                           let uu____18356 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____18347, uu____18356)  in
                                         (match uu____18342 with
=======
                                                  n_us) in
                                           let uu____18404 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18395, uu____18404) in
                                         (match uu____18390 with
>>>>>>> taramana_pointers_with_codes_modifies
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18420 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
<<<<<<< HEAD
                                                  univs_opening1 uu____18372
                                                 in
                                              let uu____18373 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____18373 with
                                               | (uu____18394,uu____18395,t3)
=======
                                                  univs_opening1 uu____18420 in
                                              let uu____18421 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18421 with
                                               | (uu____18442,uu____18443,t3)
>>>>>>> taramana_pointers_with_codes_modifies
                                                   ->
                                                   let t4 =
                                                     let uu____18458 =
                                                       let uu____18459 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
<<<<<<< HEAD
                                                         uu____18411
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18410
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____18416 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____18416 with
                           | (uu____18429,uu____18430,t1) -> t1  in
=======
                                                         uu____18459 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18458 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18464 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18464 with
                           | (uu____18477,uu____18478,t1) -> t1 in
>>>>>>> taramana_pointers_with_codes_modifies
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
                             | uu____18538 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
<<<<<<< HEAD
                             let uu____18507 =
                               let uu____18508 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____18508.FStar_Syntax_Syntax.n  in
                             match uu____18507 with
=======
                             let uu____18555 =
                               let uu____18556 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18556.FStar_Syntax_Syntax.n in
                             match uu____18555 with
>>>>>>> taramana_pointers_with_codes_modifies
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
<<<<<<< HEAD
                             | uu____18567 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____18596 =
                               let uu____18597 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____18597.FStar_Syntax_Syntax.n  in
                             match uu____18596 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18618) ->
                                 let uu____18639 = destruct_action_body body
                                    in
                                 (match uu____18639 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18684 ->
                                 let uu____18685 = destruct_action_body t  in
                                 (match uu____18685 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____18734 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____18734 with
                           | (action_univs,t) ->
                               let uu____18743 = destruct_action_typ_templ t
                                  in
                               (match uu____18743 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___241_18784 = a  in
=======
                             | uu____18615 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18644 =
                               let uu____18645 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18645.FStar_Syntax_Syntax.n in
                             match uu____18644 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18666) ->
                                 let uu____18687 = destruct_action_body body in
                                 (match uu____18687 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18732 ->
                                 let uu____18733 = destruct_action_body t in
                                 (match uu____18733 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18782 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18782 with
                           | (action_univs,t) ->
                               let uu____18791 = destruct_action_typ_templ t in
                               (match uu____18791 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___241_18832 = a in
>>>>>>> taramana_pointers_with_codes_modifies
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___241_18832.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___241_18832.FStar_Syntax_Syntax.action_unqualified_name);
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
<<<<<<< HEAD
                           let uu___242_18786 = ed  in
                           let uu____18787 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____18788 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____18789 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____18790 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____18791 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____18792 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____18793 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____18794 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____18795 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____18796 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____18797 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____18798 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____18799 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____18800 =
=======
                           let uu___242_18834 = ed in
                           let uu____18835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18838 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18839 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18840 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18841 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18843 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18844 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18845 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18846 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18847 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18848 =
>>>>>>> taramana_pointers_with_codes_modifies
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___242_18834.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___242_18834.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
<<<<<<< HEAD
                             FStar_Syntax_Syntax.ret_wp = uu____18787;
                             FStar_Syntax_Syntax.bind_wp = uu____18788;
                             FStar_Syntax_Syntax.if_then_else = uu____18789;
                             FStar_Syntax_Syntax.ite_wp = uu____18790;
                             FStar_Syntax_Syntax.stronger = uu____18791;
                             FStar_Syntax_Syntax.close_wp = uu____18792;
                             FStar_Syntax_Syntax.assert_p = uu____18793;
                             FStar_Syntax_Syntax.assume_p = uu____18794;
                             FStar_Syntax_Syntax.null_wp = uu____18795;
                             FStar_Syntax_Syntax.trivial = uu____18796;
                             FStar_Syntax_Syntax.repr = uu____18797;
                             FStar_Syntax_Syntax.return_repr = uu____18798;
                             FStar_Syntax_Syntax.bind_repr = uu____18799;
                             FStar_Syntax_Syntax.actions = uu____18800
                           }  in
                         let uu___243_18803 = s  in
=======
                             FStar_Syntax_Syntax.ret_wp = uu____18835;
                             FStar_Syntax_Syntax.bind_wp = uu____18836;
                             FStar_Syntax_Syntax.if_then_else = uu____18837;
                             FStar_Syntax_Syntax.ite_wp = uu____18838;
                             FStar_Syntax_Syntax.stronger = uu____18839;
                             FStar_Syntax_Syntax.close_wp = uu____18840;
                             FStar_Syntax_Syntax.assert_p = uu____18841;
                             FStar_Syntax_Syntax.assume_p = uu____18842;
                             FStar_Syntax_Syntax.null_wp = uu____18843;
                             FStar_Syntax_Syntax.trivial = uu____18844;
                             FStar_Syntax_Syntax.repr = uu____18845;
                             FStar_Syntax_Syntax.return_repr = uu____18846;
                             FStar_Syntax_Syntax.bind_repr = uu____18847;
                             FStar_Syntax_Syntax.actions = uu____18848
                           } in
                         let uu___243_18851 = s in
>>>>>>> taramana_pointers_with_codes_modifies
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___243_18851.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___243_18851.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___243_18851.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___243_18851.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___160_18868 =
            match uu___160_18868 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
<<<<<<< HEAD
                let uu____18847 = elim_uvars_aux_t env us [] t  in
                (match uu____18847 with
                 | (us1,uu____18871,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___244_18890 = sub_eff  in
            let uu____18891 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____18894 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
=======
                let uu____18895 = elim_uvars_aux_t env us [] t in
                (match uu____18895 with
                 | (us1,uu____18919,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___244_18938 = sub_eff in
            let uu____18939 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18942 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
>>>>>>> taramana_pointers_with_codes_modifies
            {
              FStar_Syntax_Syntax.source =
                (uu___244_18938.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
<<<<<<< HEAD
                (uu___244_18890.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18891;
              FStar_Syntax_Syntax.lift = uu____18894
            }  in
          let uu___245_18897 = s  in
=======
                (uu___244_18938.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18939;
              FStar_Syntax_Syntax.lift = uu____18942
            } in
          let uu___245_18945 = s in
>>>>>>> taramana_pointers_with_codes_modifies
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___245_18945.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_18945.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_18945.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_18945.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
<<<<<<< HEAD
          let uu____18907 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____18907 with
           | (univ_names1,binders1,comp1) ->
               let uu___246_18941 = s  in
=======
          let uu____18955 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18955 with
           | (univ_names1,binders1,comp1) ->
               let uu___246_18989 = s in
>>>>>>> taramana_pointers_with_codes_modifies
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___246_18989.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___246_18989.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___246_18989.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___246_18989.FStar_Syntax_Syntax.sigattrs)
               })
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Sig_pragma uu____18952 -> s
  
=======
      | FStar_Syntax_Syntax.Sig_pragma uu____19000 -> s
>>>>>>> taramana_pointers_with_codes_modifies
