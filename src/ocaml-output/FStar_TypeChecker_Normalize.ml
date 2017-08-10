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
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____114 -> false
  
let uu___is_Simplify : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____119 -> false
  
let uu___is_EraseUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____124 -> false
  
let uu___is_AllowUnboundUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____129 -> false
  
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
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    }
let __proj__Mkprimitive_step__item__name : primitive_step -> FStar_Ident.lid
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let __proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let __proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let __proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
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
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____384 -> false
  
type env = closure Prims.list
let closure_to_string : closure -> Prims.string =
  fun uu___145_390  ->
    match uu___145_390 with
    | Clos (uu____391,t,uu____393,uu____394) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____415 -> "Univ"
    | Dummy  -> "dummy"
  
type cfg =
  {
  steps: steps ;
  tcenv: FStar_TypeChecker_Env.env ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step Prims.list }
let __proj__Mkcfg__item__steps : cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__steps
  
let __proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__tcenv
  
let __proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__delta_level
  
let __proj__Mkcfg__item__primitive_steps : cfg -> primitive_step Prims.list =
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
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1852 ->
          let uu____1853 =
            let uu____1854 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____1854  in
          failwith uu____1853
  
let downgrade_ghost_effect_name :
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
  
let norm_universe :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____1899 =
            FStar_List.fold_left
              (fun uu____1925  ->
                 fun u1  ->
                   match uu____1925 with
                   | (cur_kernel,cur_max,out) ->
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
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2008 = FStar_List.nth env x  in
                 match uu____2008 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2012 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2021 ->
                   let uu____2022 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____2022
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2028 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2037 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2046 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2053 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2053 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2070 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2070 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2078 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
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
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec closure_as_term :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____2230  ->
             let uu____2231 = FStar_Syntax_Print.tag_of_term t  in
             let uu____2232 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2231
               uu____2232);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2233 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____2237 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____2262 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____2263 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____2264 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____2265 ->
                  let uu____2282 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars)
                     in
                  if uu____2282
                  then
                    let uu____2283 =
                      let uu____2284 =
                        FStar_Range.string_of_range
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
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2303) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
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
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
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
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
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
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2955  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
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
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___165_2998.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___165_2998.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2992))
                     in
                  (match uu____2962 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___166_3014 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___166_3014.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___166_3014.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3025,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
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
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____3085 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3085
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___167_3097 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___167_3097.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___167_3097.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43))
                       in
                    let uu___168_3098 = lb  in
                    let uu____3099 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___168_3098.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___168_3098.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3099
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
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
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3261 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3284 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3350  ->
                                        fun uu____3351  ->
                                          match (uu____3350, uu____3351) with
                                          | ((pats1,env3),(p1,b)) ->
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
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___169_3556.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___170_3575 = x  in
                                let uu____3576 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___170_3575.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___170_3575.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3576
                                }  in
                              ((let uu___171_3584 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___171_3584.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___172_3589 = x  in
                                let uu____3590 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_3589.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___172_3589.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3590
                                }  in
                              ((let uu___173_3598 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___173_3598.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___174_3608 = x  in
                                let uu____3609 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___174_3608.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___174_3608.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3609
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___175_3618 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___175_3618.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____3621 = norm_pat env1 pat  in
                        (match uu____3621 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
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
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____3768 -> closure_as_term cfg env t

and closures_as_args_delayed :
  cfg ->
    closure Prims.list ->
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
        | uu____3792 ->
            FStar_List.map
              (fun uu____3811  ->
                 match uu____3811 with
                 | (x,imp) ->
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
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____3846 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3901  ->
                  fun uu____3902  ->
                    match (uu____3901, uu____3902) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___176_3984 = b  in
                          let uu____3985 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___176_3984.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
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
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____4066 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4081 = closure_as_term_delayed cfg env t  in
                 let uu____4082 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4081 uu____4082
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4095 = closure_as_term_delayed cfg env t  in
                 let uu____4096 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4095 uu____4096
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
                        (fun uu___148_4122  ->
                           match uu___148_4122 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4126 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____4126
                           | f -> f))
                    in
                 let uu____4130 =
                   let uu___177_4131 = c1  in
                   let uu____4132 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4132;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___177_4131.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
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
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___150_4166  ->
                      match uu___150_4166 with
                      | FStar_Syntax_Syntax.DECREASES uu____4167 -> false
                      | uu____4170 -> true))
               in
            let rc1 =
              let uu___178_4172 = rc  in
              let uu____4173 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___178_4172.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4173;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
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
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4322;
                FStar_Syntax_Syntax.vars = uu____4323;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4325;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4326;_},uu____4327)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
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
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____4464)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____4469 -> FStar_Pervasives_Native.None)
     in
  let arg_as_list f uu____4495 =
    match uu____4495 with
    | (a,uu____4509) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4538 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4555 = sequence xs  in
              (match uu____4555 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs'))
           in
        let uu____4575 = FStar_Syntax_Util.list_elements a  in
        (match uu____4575 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4593 =
               FStar_List.map
                 (fun x  ->
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
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
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
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f }
     in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4870 = f x  in int_as_const r uu____4870)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4898 = f x y  in int_as_const r uu____4898)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  -> let uu____4919 = f x  in bool_as_const r uu____4919)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4947 = f x y  in bool_as_const r uu____4947)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4975 = f x y  in string_as_const r uu____4975)
     in
  let list_of_string' rng s =
    let name l =
      let uu____4989 =
        let uu____4990 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
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
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in int_as_const rng r  in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
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
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false")  in
  let string_of_int2 rng i =
    let uu____5136 = FStar_Util.string_of_int i  in
    string_as_const rng uu____5136  in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false")  in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let range_of1 uu____5166 args =
    match args with
    | uu____5178::(t,uu____5180)::[] ->
        let uu____5209 = term_of_range t.FStar_Syntax_Syntax.pos  in
        FStar_Pervasives_Native.Some uu____5209
    | uu____5214 -> FStar_Pervasives_Native.None  in
  let set_range_of1 r args =
    match args with
    | uu____5252::(t,uu____5254)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____5256;
                                     FStar_Syntax_Syntax.vars = uu____5257;_},uu____5258)::[]
        ->
        FStar_Pervasives_Native.Some
          (let uu___179_5300 = t  in
           {
             FStar_Syntax_Syntax.n = (uu___179_5300.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___179_5300.FStar_Syntax_Syntax.vars)
           })
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
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r1 =
               let uu____5448 = FStar_Range.mk_pos from_l from_c  in
               let uu____5449 = FStar_Range.mk_pos to_l to_c  in
               FStar_Range.mk_range fn1 uu____5448 uu____5449  in
             let uu____5450 = term_of_range r1  in
             FStar_Pervasives_Native.Some uu____5450
         | uu____5455 -> FStar_Pervasives_Native.None)
    | uu____5476 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng
       in
    match args with
    | (_typ,uu____5506)::(a1,uu____5508)::(a2,uu____5510)::[] ->
        let uu____5547 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____5547 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5560 -> FStar_Pervasives_Native.None)
    | uu____5561 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____5579 =
      let uu____5594 =
        let uu____5609 =
          let uu____5624 =
            let uu____5639 =
              let uu____5654 =
                let uu____5669 =
                  let uu____5684 =
                    let uu____5699 =
                      let uu____5714 =
                        let uu____5729 =
                          let uu____5744 =
                            let uu____5759 =
                              let uu____5774 =
                                let uu____5789 =
                                  let uu____5804 =
                                    let uu____5819 =
                                      let uu____5834 =
                                        let uu____5849 =
                                          let uu____5864 =
                                            let uu____5879 =
                                              let uu____5892 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
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
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
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
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5789
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
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
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
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
                {
                  FStar_Syntax_Syntax.n =
                    (uu___180_7134.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___180_7134.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___181_7138 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___181_7138.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___181_7138.FStar_Syntax_Syntax.vars)
                })
         | uu____7139 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7141)::uu____7142::(a1,uu____7144)::(a2,uu____7146)::[] ->
        let uu____7195 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7195 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___180_7201 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___180_7201.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___180_7201.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___181_7205 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___181_7205.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___181_7205.FStar_Syntax_Syntax.vars)
                })
         | uu____7206 -> FStar_Pervasives_Native.None)
    | uu____7207 -> failwith "Unexpected number of arguments"  in
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
    }  in
  [propositional_equality; hetero_propositional_equality] 
let reduce_primops :
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____7220 =
        FStar_All.pipe_left Prims.op_Negation
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
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7264 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps
                     in
                  (match uu____7264 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7277 =
                            prim_step.interpretation
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
         {
           steps = [Primops];
           tcenv = (uu___182_7292.tcenv);
           delta_level = (uu___182_7292.delta_level);
           primitive_steps = equality_ops
         }) tm
  
let maybe_simplify :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      let steps = cfg.steps  in
      let w t =
        let uu___183_7316 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___183_7316.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___183_7316.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7333 -> FStar_Pervasives_Native.None  in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg)
         in
      let tm1 = reduce_primops cfg tm  in
      let uu____7373 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps)
         in
      if uu____7373
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7376;
                     FStar_Syntax_Syntax.vars = uu____7377;_},uu____7378);
                FStar_Syntax_Syntax.pos = uu____7379;
                FStar_Syntax_Syntax.vars = uu____7380;_},args)
             ->
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
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7598)::uu____7599::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7662::(FStar_Pervasives_Native.Some (false
                               ),uu____7663)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7726 -> tm1)
             else
               (let uu____7742 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid
                   in
                if uu____7742
                then
                  let uu____7743 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____7743 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7798)::uu____7799::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7862::(FStar_Pervasives_Native.Some (true
                                 ),uu____7863)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7926)::
                      (uu____7927,(arg,uu____7929))::[] -> arg
                  | (uu____7994,(arg,uu____7996))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____7997)::[]
                      -> arg
                  | uu____8062 -> tm1
                else
                  (let uu____8078 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
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
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8198)::uu____8199::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8262)::
                         (uu____8263,(arg,uu____8265))::[] -> arg
                     | (uu____8330,(p,uu____8332))::(uu____8333,(q,uu____8335))::[]
                         ->
                         let uu____8400 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8400
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8402 -> tm1
                   else
                     (let uu____8418 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8418
                      then
                        let uu____8419 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____8419 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8474)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8513)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8552 -> tm1
                      else
                        (let uu____8568 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
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
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8591::[],body,uu____8593) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
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
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8670::[],body,uu____8672) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8699 -> tm1)
                                | uu____8702 -> tm1)
                           | uu____8703 -> tm1
                         else
                           (let uu____8713 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
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
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8736::[],body,uu____8738) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
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
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8815::[],body,uu____8817) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8844 -> tm1)
                                   | uu____8847 -> tm1)
                              | uu____8848 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8859;
                FStar_Syntax_Syntax.vars = uu____8860;_},args)
             ->
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
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9074)::uu____9075::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9138::(FStar_Pervasives_Native.Some (false
                               ),uu____9139)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9202 -> tm1)
             else
               (let uu____9218 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid
                   in
                if uu____9218
                then
                  let uu____9219 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____9219 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9274)::uu____9275::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9338::(FStar_Pervasives_Native.Some (true
                                 ),uu____9339)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9402)::
                      (uu____9403,(arg,uu____9405))::[] -> arg
                  | (uu____9470,(arg,uu____9472))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9473)::[]
                      -> arg
                  | uu____9538 -> tm1
                else
                  (let uu____9554 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
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
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9674)::uu____9675::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9738)::
                         (uu____9739,(arg,uu____9741))::[] -> arg
                     | (uu____9806,(p,uu____9808))::(uu____9809,(q,uu____9811))::[]
                         ->
                         let uu____9876 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____9876
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9878 -> tm1
                   else
                     (let uu____9894 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____9894
                      then
                        let uu____9895 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____9895 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9950)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9989)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10028 -> tm1
                      else
                        (let uu____10044 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
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
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10067::[],body,uu____10069) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
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
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10146::[],body,uu____10148) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10175 -> tm1)
                                | uu____10178 -> tm1)
                           | uu____10179 -> tm1
                         else
                           (let uu____10189 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
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
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10212::[],body,uu____10214) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
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
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10291::[],body,uu____10293) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10320 -> tm1)
                                   | uu____10323 -> tm1)
                              | uu____10324 -> tm1
                            else reduce_equality cfg tm1)))))
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
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10373::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10378::uu____10379::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10382 -> false
  
let get_norm_request :
  'Auu____10395 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10395) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let unembed_step s1 =
          let uu____10437 =
            let uu____10438 = FStar_Syntax_Util.un_uinst s1  in
            uu____10438.FStar_Syntax_Syntax.n  in
          match uu____10437 with
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
                 FStar_Syntax_Syntax.pos = uu____10447;
                 FStar_Syntax_Syntax.vars = uu____10448;_},(names1,uu____10450)::[])
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
          | uu____10489 -> failwith "Not an embedded `Prims.step`"  in
        FStar_Syntax_Embeddings.unembed_list unembed_step s  in
      match args with
      | uu____10496::(tm,uu____10498)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____10521)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____10536)::uu____10537::(tm,uu____10539)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
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
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10612;
           FStar_Syntax_Syntax.vars = uu____10613;_},uu____10614,uu____10615))::uu____10616
        -> true
    | uu____10623 -> false
  
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
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
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10759
                 uu____10760 uu____10761);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10788 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10813 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10830 =
                 let uu____10831 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos  in
                 let uu____10832 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10831 uu____10832
                  in
               failwith uu____10830
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10833 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10850 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10851 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10852;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10853;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10856;
                 FStar_Syntax_Syntax.fv_delta = uu____10857;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10858;
                 FStar_Syntax_Syntax.fv_delta = uu____10859;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10860);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args  in
               let hd2 = closure_as_term cfg env hd1  in
               let t2 =
                 let uu___184_10902 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___184_10902.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___184_10902.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10935 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____10935) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___185_10943 = cfg  in
                 let uu____10944 =
                   FStar_List.filter
                     (fun uu___152_10947  ->
                        match uu___152_10947 with
                        | UnfoldOnly uu____10948 -> false
                        | NoDeltaSteps  -> false
                        | uu____10951 -> true) cfg.steps
                    in
                 {
                   steps = uu____10944;
                   tcenv = (uu___185_10943.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___185_10943.primitive_steps)
                 }  in
               let uu____10952 = get_norm_request (norm cfg' env []) args  in
               (match uu____10952 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10968 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___153_10973  ->
                                match uu___153_10973 with
                                | UnfoldUntil uu____10974 -> true
                                | UnfoldOnly uu____10975 -> true
                                | uu____10978 -> false))
                         in
                      if uu____10968
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___186_10983 = cfg  in
                      {
                        steps = s;
                        tcenv = (uu___186_10983.tcenv);
                        delta_level;
                        primitive_steps = (uu___186_10983.primitive_steps)
                      }  in
                    let stack' = (Debug t1) ::
                      (Steps
                         ((cfg.steps), (cfg.primitive_steps),
                           (cfg.delta_level)))
                      :: stack1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10991;
                  FStar_Syntax_Syntax.vars = uu____10992;_},a1::a2::rest)
               ->
               let uu____11040 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11040 with
                | (hd1,uu____11056) ->
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
                    (FStar_Const.Const_reflect uu____11121);
                  FStar_Syntax_Syntax.pos = uu____11122;
                  FStar_Syntax_Syntax.vars = uu____11123;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11155 = FStar_List.tl stack1  in
               norm cfg env uu____11155 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11158;
                  FStar_Syntax_Syntax.vars = uu____11159;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11191 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____11191 with
                | (reify_head,uu____11207) ->
                    let a1 =
                      let uu____11229 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a)
                         in
                      FStar_Syntax_Subst.compress uu____11229  in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11232);
                            FStar_Syntax_Syntax.pos = uu____11233;
                            FStar_Syntax_Syntax.vars = uu____11234;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11268 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1  in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____11278 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack1 uu____11278
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11285 =
                 FStar_All.pipe_right cfg.steps
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
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1  in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___154_11309  ->
                         match uu___154_11309 with
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
                 let uu____11312 =
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
                           FStar_Parser_Const.false_lid))
                    in
                 if uu____11312
                 then false
                 else
                   (let uu____11314 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___155_11321  ->
                              match uu___155_11321 with
                              | UnfoldOnly uu____11322 -> true
                              | uu____11325 -> false))
                       in
                    match uu____11314 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11329 -> should_delta)
                  in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____11334 = FStar_Syntax_Syntax.range_of_fv f  in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____11334  in
                  let uu____11335 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  match uu____11335 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____11348  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____11359  ->
                            let uu____11360 =
                              FStar_Syntax_Print.term_to_string t0  in
                            let uu____11361 =
                              FStar_Syntax_Print.term_to_string t2  in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____11360 uu____11361);
                       (let t3 =
                          let uu____11363 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant))
                             in
                          if uu____11363
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
                          | (UnivArgs (us',uu____11373))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env)
                                 in
                              norm cfg env1 stack2 t3
                          | uu____11396 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____11397 ->
                              let uu____11398 =
                                let uu____11399 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____11399
                                 in
                              failwith uu____11398
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11402 = lookup_bvar env x  in
               (match uu____11402 with
                | Univ uu____11403 ->
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
                                 norm cfg env2 stack1 t'
                             | uu____11533 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11585)::uu____11586 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11595)::uu____11596 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11606,uu____11607))::stack_rest ->
                    (match c with
                     | Univ uu____11611 -> norm cfg (c :: env) stack_rest t1
                     | uu____11612 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11617::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11633  ->
                                         let uu____11634 =
                                           closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11634);
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
                                           (fun uu___156_11639  ->
                                              match uu___156_11639 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11640 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11644  ->
                                         let uu____11645 =
                                           closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11645);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11646 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11649 ->
                                   let cfg1 =
                                     let uu___187_11653 = cfg  in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___187_11653.tcenv);
                                       delta_level =
                                         (uu___187_11653.delta_level);
                                       primitive_steps =
                                         (uu___187_11653.primitive_steps)
                                     }  in
                                   let uu____11654 =
                                     closure_as_term cfg1 env t1  in
                                   rebuild cfg1 env stack1 uu____11654)
                          | uu____11655::tl1 ->
                              (log cfg
                                 (fun uu____11674  ->
                                    let uu____11675 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11675);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___188_11705 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___188_11705.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11766  ->
                          let uu____11767 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11767);
                     norm cfg env stack2 t1)
                | (Debug uu____11768)::uu____11769 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11772 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____11772
                    else
                      (let uu____11774 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11774 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11798  -> Dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11814 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____11814
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11824 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11824)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_11829 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_11829.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_11829.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11830 -> lopt  in
                           (log cfg
                              (fun uu____11836  ->
                                 let uu____11837 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11837);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___190_11850 = cfg  in
                               let uu____11851 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___190_11850.steps);
                                 tcenv = (uu___190_11850.tcenv);
                                 delta_level = (uu___190_11850.delta_level);
                                 primitive_steps = uu____11851
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11860)::uu____11861 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11868 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____11868
                    else
                      (let uu____11870 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11870 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11894  -> Dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11910 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____11910
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11920 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11920)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_11925 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_11925.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_11925.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11926 -> lopt  in
                           (log cfg
                              (fun uu____11932  ->
                                 let uu____11933 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11933);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___190_11946 = cfg  in
                               let uu____11947 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___190_11946.steps);
                                 tcenv = (uu___190_11946.tcenv);
                                 delta_level = (uu___190_11946.delta_level);
                                 primitive_steps = uu____11947
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11956)::uu____11957 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11968 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____11968
                    else
                      (let uu____11970 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11970 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11994  -> Dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12010 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12010
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12020 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12020)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12025 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12025.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12025.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12026 -> lopt  in
                           (log cfg
                              (fun uu____12032  ->
                                 let uu____12033 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12033);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___190_12046 = cfg  in
                               let uu____12047 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___190_12046.steps);
                                 tcenv = (uu___190_12046.tcenv);
                                 delta_level = (uu___190_12046.delta_level);
                                 primitive_steps = uu____12047
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12056)::uu____12057 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12066 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____12066
                    else
                      (let uu____12068 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12068 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12092  -> Dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12108 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12108
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12118 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12118)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12123 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12123.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12123.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12124 -> lopt  in
                           (log cfg
                              (fun uu____12130  ->
                                 let uu____12131 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12131);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___190_12144 = cfg  in
                               let uu____12145 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___190_12144.steps);
                                 tcenv = (uu___190_12144.tcenv);
                                 delta_level = (uu___190_12144.delta_level);
                                 primitive_steps = uu____12145
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12154)::uu____12155 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12170 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____12170
                    else
                      (let uu____12172 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12172 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12196  -> Dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12212 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12212
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12222 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12222)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12227 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12227.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12227.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12228 -> lopt  in
                           (log cfg
                              (fun uu____12234  ->
                                 let uu____12235 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12235);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___190_12248 = cfg  in
                               let uu____12249 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___190_12248.steps);
                                 tcenv = (uu___190_12248.tcenv);
                                 delta_level = (uu___190_12248.delta_level);
                                 primitive_steps = uu____12249
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12258 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____12258
                    else
                      (let uu____12260 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12260 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12284  -> Dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12300 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars)
                                      in
                                   if uu____12300
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12310 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12310)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___189_12315 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___189_12315.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___189_12315.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12316 -> lopt  in
                           (log cfg
                              (fun uu____12322  ->
                                 let uu____12323 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12323);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___190_12336 = cfg  in
                               let uu____12337 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___190_12336.steps);
                                 tcenv = (uu___190_12336.tcenv);
                                 delta_level = (uu___190_12336.delta_level);
                                 primitive_steps = uu____12337
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12384  ->
                         fun stack2  ->
                           match uu____12384 with
                           | (a,aq) ->
                               let uu____12396 =
                                 let uu____12397 =
                                   let uu____12404 =
                                     let uu____12405 =
                                       let uu____12424 =
                                         FStar_Util.mk_ref
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
               (log cfg
                  (fun uu____12476  ->
                     let uu____12477 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12477);
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
                             ((let uu___191_12501 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___191_12501.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___191_12501.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack1 t2
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
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1  in
                      let t2 =
                        let uu____12535 =
                          let uu____12536 =
                            let uu____12543 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___192_12545 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___192_12545.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___192_12545.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12543)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12536  in
                        mk uu____12535 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12564 = closure_as_term cfg env t1  in
                 rebuild cfg env stack1 uu____12564
               else
                 (let uu____12566 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12566 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12574 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12586  -> Dummy :: env1) env)
                           in
                        norm_comp cfg uu____12574 c1  in
                      let t2 =
                        let uu____12596 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12596 c2  in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12655)::uu____12656 -> norm cfg env stack1 t11
                | (Arg uu____12665)::uu____12666 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12675;
                       FStar_Syntax_Syntax.vars = uu____12676;_},uu____12677,uu____12678))::uu____12679
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12686)::uu____12687 ->
                    norm cfg env stack1 t11
                | uu____12696 ->
                    let t12 = norm cfg env [] t11  in
                    (log cfg
                       (fun uu____12700  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
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
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1  in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12836,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12837;
                               FStar_Syntax_Syntax.lbunivs = uu____12838;
                               FStar_Syntax_Syntax.lbtyp = uu____12839;
                               FStar_Syntax_Syntax.lbeff = uu____12840;
                               FStar_Syntax_Syntax.lbdef = uu____12841;_}::uu____12842),uu____12843)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12879 =
                 (let uu____12882 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____12882) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12884 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
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
                 norm cfg env1 stack1 body
               else
                 (let uu____12960 =
                    let uu____12965 =
                      let uu____12966 =
                        let uu____12967 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left
                           in
                        FStar_All.pipe_right uu____12967
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [uu____12966]  in
                    FStar_Syntax_Subst.open_term uu____12965 body  in
                  match uu____12960 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let lbname =
                        let x =
                          let uu____12981 = FStar_List.hd bs  in
                          FStar_Pervasives_Native.fst uu____12981  in
                        FStar_Util.Inl
                          (let uu___193_12991 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_12991.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_12991.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           })
                         in
                      let lb1 =
                        let uu___194_12993 = lb  in
                        let uu____12994 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___194_12993.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___194_12993.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____12994
                        }  in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13011  -> Dummy :: env1)
                             env)
                         in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____13034 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13034 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13070 =
                               let uu___195_13071 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___195_13071.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___195_13071.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13070  in
                           let uu____13072 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13072 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
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
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___196_13121.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13122;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___196_13121.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13120
                                 | uu____13129 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___197_13133 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___197_13133.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___197_13133.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1
                       in
                    let env' =
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
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___198_13159.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___198_13159.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13186 = closure_as_term cfg env t1  in
               rebuild cfg env stack1 uu____13186
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13205 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13256  ->
                        match uu____13256 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13329 =
                                let uu___199_13330 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___199_13330.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___199_13330.FStar_Syntax_Syntax.sort)
                                }  in
                              FStar_Syntax_Syntax.bv_to_tm uu____13329  in
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
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____13205 with
                | (rec_env,memos,uu____13458) ->
                    let uu____13487 =
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
                             let uu____13892 =
                               let uu____13893 =
                                 let uu____13912 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None
                                    in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13912, false)
                                  in
                               Clos uu____13893  in
                             uu____13892 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
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
                             FStar_Syntax_Syntax.pos = uu____13980;
                             FStar_Syntax_Syntax.vars = uu____13981;_},uu____13982,uu____13983))::uu____13984
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____13991 -> false  in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2  in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1  in
                      let cfg1 =
                        let uu____14001 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations)
                           in
                        if uu____14001
                        then
                          let uu___200_14002 = cfg  in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___200_14002.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___200_14002.primitive_steps)
                          }
                        else
                          (let uu___201_14004 = cfg  in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___201_14004.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___201_14004.primitive_steps)
                           })
                         in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
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
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14032 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14040 =
                                         let uu____14041 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____14041.FStar_Syntax_Syntax.n
                                          in
                                       match uu____14040 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14047,uu____14048))
                                           ->
                                           let uu____14057 =
                                             let uu____14058 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____14058.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____14057 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14064,msrc,uu____14066))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14075 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14075
                                            | uu____14076 ->
                                                FStar_Pervasives_Native.None)
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
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___202_14083.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___202_14083.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___202_14083.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            }  in
                                          let uu____14084 =
                                            FStar_List.tl stack1  in
                                          let uu____14085 =
                                            let uu____14086 =
                                              let uu____14089 =
                                                let uu____14090 =
                                                  let uu____14103 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
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
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14124;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14125;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14130 -> false  in
                                          if uu____14119
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
                                               let uu____14154 =
                                                 let uu____14157 =
                                                   let uu____14158 =
                                                     let uu____14175 =
                                                       let uu____14178 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____14178]  in
                                                     (uu____14175, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc))
                                                      in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14158
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14157
                                                  in
                                               uu____14154
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos
                                                in
                                             let close1 =
                                               closure_as_term cfg env  in
                                             let bind_inst =
                                               let uu____14194 =
                                                 let uu____14195 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr
                                                    in
                                                 uu____14195.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____14194 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14201::uu____14202::[])
                                                   ->
                                                   let uu____14209 =
                                                     let uu____14212 =
                                                       let uu____14213 =
                                                         let uu____14220 =
                                                           let uu____14223 =
                                                             let uu____14224
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp
                                                                in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
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
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14237 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects"
                                                in
                                             let reified =
                                               let uu____14243 =
                                                 let uu____14246 =
                                                   let uu____14247 =
                                                     let uu____14262 =
                                                       let uu____14265 =
                                                         FStar_Syntax_Syntax.as_arg
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
                                                               =
                                                               let uu____14281
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let uu____14282
                                                                 =
                                                                 let uu____14285
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
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
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14378
                                      ->
                                      let head3 = norm cfg env [] head2  in
                                      let action_unfolded =
                                        let uu____14383 =
                                          maybe_extract_fv head3  in
                                        match uu____14383 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14388 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14389 ->
                                            FStar_Pervasives_Native.Some
                                              false
                                         in
                                      (head3, action_unfolded)
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
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
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
                                  then
                                    let uu____14446 =
                                      let uu____14447 =
                                        FStar_Syntax_Print.term_to_string
                                          head1
                                         in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14447
                                       in
                                    failwith uu____14446
                                  else ());
                                 (let uu____14449 =
                                    maybe_unfold_action head_app  in
                                  match uu____14449 with
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
                                      let uu____14488 = FStar_List.tl stack1
                                         in
                                      norm cfg env uu____14488 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14502 = closure_as_term cfg env t'  in
                             reify_lift cfg.tcenv e msrc mtgt uu____14502  in
                           let uu____14503 = FStar_List.tl stack1  in
                           norm cfg env uu____14503 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14624  ->
                                     match uu____14624 with
                                     | (pat,wopt,tm) ->
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
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14714;
                             FStar_Syntax_Syntax.vars = uu____14715;_},uu____14716,uu____14717))::uu____14718
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
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
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations))
                          in
                       if uu____14731
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1  in
                         let cfg1 =
                           let uu___203_14740 = cfg  in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___203_14740.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___203_14740.primitive_steps)
                           }  in
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
                | uu____14742 ->
                    (match stack1 with
                     | uu____14743::uu____14744 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14749) ->
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
                          | uu____14774 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1  in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14788 =
                                 norm_pattern_args cfg env args  in
                               FStar_Syntax_Syntax.Meta_pattern uu____14788
                           | uu____14799 -> m  in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack1 t2)))

and reify_lift :
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
               | FStar_Pervasives_Native.None  ->
                   let uu____14898 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____14898
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14899;
                     FStar_TypeChecker_Env.mtarget = uu____14900;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14901;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14912;
                     FStar_TypeChecker_Env.mtarget = uu____14913;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14914;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
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
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____14988  ->
                   match uu____14988 with
                   | (a,imp) ->
                       let uu____14999 = norm cfg env [] a  in
                       (uu____14999, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp  in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___204_15016 = comp1  in
            let uu____15019 =
              let uu____15020 =
                let uu____15029 = norm cfg env [] t  in
                let uu____15030 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15029, uu____15030)  in
              FStar_Syntax_Syntax.Total uu____15020  in
            {
              FStar_Syntax_Syntax.n = uu____15019;
              FStar_Syntax_Syntax.pos =
                (uu___204_15016.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___204_15016.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___205_15045 = comp1  in
            let uu____15048 =
              let uu____15049 =
                let uu____15058 = norm cfg env [] t  in
                let uu____15059 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15058, uu____15059)  in
              FStar_Syntax_Syntax.GTotal uu____15049  in
            {
              FStar_Syntax_Syntax.n = uu____15048;
              FStar_Syntax_Syntax.pos =
                (uu___205_15045.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___205_15045.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15111  ->
                      match uu____15111 with
                      | (a,i) ->
                          let uu____15122 = norm cfg env [] a  in
                          (uu____15122, i)))
               in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___157_15133  ->
                      match uu___157_15133 with
                      | FStar_Syntax_Syntax.DECREASES t ->
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
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15147;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___207_15146.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15148;
                  FStar_Syntax_Syntax.effect_args = uu____15151;
                  FStar_Syntax_Syntax.flags = flags
                }  in
              FStar_Syntax_Syntax.Comp uu____15145  in
            {
              FStar_Syntax_Syntax.n = uu____15144;
              FStar_Syntax_Syntax.pos =
                (uu___206_15141.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___206_15141.FStar_Syntax_Syntax.vars)
            }

and ghost_to_pure_aux :
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
            (let uu___208_15169 = cfg  in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___208_15169.tcenv);
               delta_level = (uu___208_15169.delta_level);
               primitive_steps = (uu___208_15169.primitive_steps)
             }) env [] t
           in
        let non_info t =
          let uu____15174 = norm1 t  in
          FStar_Syntax_Util.non_informative uu____15174  in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15177 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___209_15196 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___209_15196.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___209_15196.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name
               in
            let uu____15203 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ)
               in
            if uu____15203
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
                      else ct.FStar_Syntax_Syntax.flags  in
                    let uu___210_15214 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___210_15214.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___210_15214.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___210_15214.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                       in
                    let uu___211_15216 = ct1  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___211_15216.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___211_15216.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___211_15216.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___211_15216.FStar_Syntax_Syntax.flags)
                    }
                 in
              let uu___212_15217 = c  in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___212_15217.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___212_15217.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15219 -> c

and norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15222  ->
        match uu____15222 with
        | (x,imp) ->
            let uu____15225 =
              let uu___213_15226 = x  in
              let uu____15227 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___213_15226.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___213_15226.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15227
              }  in
            (uu____15225, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15233 =
          FStar_List.fold_left
            (fun uu____15251  ->
               fun b  ->
                 match uu____15251 with
                 | (nbs',env1) ->
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
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____15295 =
              let uu___214_15296 = rc  in
              let uu____15297 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___214_15296.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15297;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___214_15296.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15295
        | uu____15304 -> lopt

and rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          match stack1 with
          | [] -> t
          | (Debug tm)::stack2 ->
              ((let uu____15316 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms")
                   in
                if uu____15316
                then
                  let uu____15317 = FStar_Syntax_Print.term_to_string tm  in
                  let uu____15318 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____15317
                    uu____15318
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___215_15336 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___215_15336.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15405  ->
                    let uu____15406 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15406);
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
              let bs1 = norm_binders cfg env' bs  in
              let lopt1 = norm_lcomp_opt cfg env'' lopt  in
              let uu____15442 =
                let uu___216_15443 = FStar_Syntax_Util.abs bs1 t lopt1  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___216_15443.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___216_15443.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack2 uu____15442
          | (Arg (Univ uu____15444,uu____15445,uu____15446))::uu____15447 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15450,uu____15451))::uu____15452 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15468),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15497  ->
                    let uu____15498 = FStar_Syntax_Print.term_to_string tm
                       in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15498);
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
                 (let uu____15508 = FStar_ST.op_Bang m  in
                  match uu____15508 with
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
                  | FStar_Pervasives_Native.Some (uu____15608,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r
                         in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
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
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___158_15701  ->
                               match uu___158_15701 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15702 -> false))
                        in
                     let steps' =
                       let uu____15706 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations)
                          in
                       if uu____15706
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta]  in
                     let uu___217_15710 = cfg  in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___217_15710.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___217_15710.primitive_steps)
                     }  in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1  in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15754 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15777 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15843  ->
                                   fun uu____15844  ->
                                     match (uu____15843, uu____15844) with
                                     | ((pats1,env3),(p1,b)) ->
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
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___218_16049.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___219_16068 = x  in
                           let uu____16069 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___219_16068.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___219_16068.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16069
                           }  in
                         ((let uu___220_16077 = p  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___220_16077.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___221_16082 = x  in
                           let uu____16083 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___221_16082.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___221_16082.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16083
                           }  in
                         ((let uu___222_16091 = p  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___222_16091.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___223_16101 = x  in
                           let uu____16102 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___223_16101.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___223_16101.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16102
                           }  in
                         let t2 = norm_or_whnf env2 t1  in
                         ((let uu___224_16111 = p  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___224_16111.FStar_Syntax_Syntax.p)
                           }), env2)
                      in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____16115 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16129 =
                                   FStar_Syntax_Subst.open_branch branch1  in
                                 match uu____16129 with
                                 | (p,wopt,e) ->
                                     let uu____16149 = norm_pat env1 p  in
                                     (match uu____16149 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
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
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16196) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16201 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16202;
                        FStar_Syntax_Syntax.fv_delta = uu____16203;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16204;
                        FStar_Syntax_Syntax.fv_delta = uu____16205;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16206);_}
                      -> true
                  | uu____16213 -> false  in
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
                  let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                     in
                  let uu____16342 =
                    FStar_Syntax_Util.head_and_args scrutinee1  in
                  match uu____16342 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16391 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16394 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16397 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
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
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16577 -> FStar_Util.Inr false
                 in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16679 = matches_pat scrutinee1 p1  in
                      (match uu____16679 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
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
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16700 uu____16701);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16719 =
                                        let uu____16720 =
                                          let uu____16739 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
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
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___159_16816  ->
                match uu___159_16816 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16820 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16826 -> d  in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps
      }
  
let normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e  in
          let c1 =
            let uu___225_16855 = config s e  in
            {
              steps = (uu___225_16855.steps);
              tcenv = (uu___225_16855.tcenv);
              delta_level = (uu___225_16855.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps)
            }  in
          norm c1 [] [] t
  
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
        let uu____16912 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____16912  in
      let uu____16913 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____16913
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___226_16915 = lc  in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___226_16915.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___226_16915.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16918  ->
                    let uu____16919 = lc.FStar_Syntax_Syntax.comp ()  in
                    ghost_to_pure env uu____16919))
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____16938 = FStar_Util.message_of_exn e  in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16938);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
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
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
  
let reduce_or_remove_uvar_solutions :
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
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17125 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____17125 with
                         | (binders,args) ->
                             let uu____17142 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____17142
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
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
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17262 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___231_17270 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___231_17270.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___231_17270.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___231_17270.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___231_17270.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___231_17270.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___231_17270.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___231_17270.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___231_17270.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___231_17270.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___231_17270.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___231_17270.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___231_17270.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___231_17270.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___231_17270.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___231_17270.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___231_17270.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___231_17270.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___231_17270.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___231_17270.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___231_17270.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___231_17270.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___231_17270.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___231_17270.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___231_17270.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___231_17270.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___231_17270.FStar_TypeChecker_Env.identifier_info)
                                 }) t
                               in
                            match uu____17262 with
                            | (uu____17271,ty,uu____17273) ->
                                eta_expand_with_type env t ty))
                | uu____17274 ->
                    let uu____17275 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___232_17283 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___232_17283.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___232_17283.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___232_17283.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___232_17283.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___232_17283.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___232_17283.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___232_17283.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___232_17283.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___232_17283.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___232_17283.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___232_17283.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___232_17283.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___232_17283.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___232_17283.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___232_17283.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___232_17283.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___232_17283.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___232_17283.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___232_17283.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.type_of =
                             (uu___232_17283.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___232_17283.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___232_17283.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___232_17283.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___232_17283.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___232_17283.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
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
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____17364,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
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
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17515) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17552) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17591,FStar_Util.Inl uu____17592) ->
                         ([], (FStar_Util.Inl t3))
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
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
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
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
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
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17916 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____17916 with
           | (univ_names1,binders1,typ1) ->
               let uu___233_17944 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___233_17944.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___233_17944.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___233_17944.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___233_17944.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___234_17965 = s  in
          let uu____17966 =
            let uu____17967 =
              let uu____17976 = FStar_List.map (elim_uvars env) sigs  in
              (uu____17976, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____17967  in
          {
            FStar_Syntax_Syntax.sigel = uu____17966;
            FStar_Syntax_Syntax.sigrng =
              (uu___234_17965.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___234_17965.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___234_17965.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___234_17965.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____17993 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____17993 with
           | (univ_names1,uu____18011,typ1) ->
               let uu___235_18025 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_18025.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_18025.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_18025.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_18025.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18031 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____18031 with
           | (univ_names1,uu____18049,typ1) ->
               let uu___236_18063 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___236_18063.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___236_18063.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___236_18063.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___236_18063.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18097 =
                      FStar_Syntax_Subst.univ_var_opening
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
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___237_18124.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___237_18124.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        }))
             in
          let uu___238_18125 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___238_18125.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___238_18125.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___238_18125.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___238_18125.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___239_18137 = s  in
          let uu____18138 =
            let uu____18139 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____18139  in
          {
            FStar_Syntax_Syntax.sigel = uu____18138;
            FStar_Syntax_Syntax.sigrng =
              (uu___239_18137.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___239_18137.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___239_18137.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___239_18137.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18143 = elim_uvars_aux_t env us [] t  in
          (match uu____18143 with
           | (us1,uu____18161,t1) ->
               let uu___240_18175 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_18175.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_18175.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_18175.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_18175.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18176 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18178 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
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
                                | (us1,t1) ->
                                    let uu____18317 =
                                      let uu____18322 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____18329 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____18322, uu____18329)  in
                                    (match uu____18317 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18342 =
                                           let uu____18347 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
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
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18372 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18372
                                                 in
                                              let uu____18373 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____18373 with
                                               | (uu____18394,uu____18395,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18410 =
                                                       let uu____18411 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
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
                             | uu____18490 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____18507 =
                               let uu____18508 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____18508.FStar_Syntax_Syntax.n  in
                             match uu____18507 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
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
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___241_18784.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___241_18784.FStar_Syntax_Syntax.action_unqualified_name);
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
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___242_18786.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___242_18786.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
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
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___243_18803.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___243_18803.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___243_18803.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___243_18803.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___160_18820 =
            match uu___160_18820 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
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
            {
              FStar_Syntax_Syntax.source =
                (uu___244_18890.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___244_18890.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18891;
              FStar_Syntax_Syntax.lift = uu____18894
            }  in
          let uu___245_18897 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___245_18897.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_18897.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_18897.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_18897.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18907 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____18907 with
           | (univ_names1,binders1,comp1) ->
               let uu___246_18941 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___246_18941.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___246_18941.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___246_18941.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___246_18941.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18952 -> s
  