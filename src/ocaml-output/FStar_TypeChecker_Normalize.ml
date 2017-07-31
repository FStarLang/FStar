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
type steps = step Prims.list
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__interpretation:
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
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____303 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list,FStar_Syntax_Syntax.term,(closure Prims.list,
                                                   FStar_Syntax_Syntax.term)
                                                   FStar_Pervasives_Native.tuple2
                                                   FStar_Syntax_Syntax.memo,
      Prims.bool) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____371 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____384 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___144_390  ->
    match uu___144_390 with
    | Clos (uu____391,t,uu____393,uu____394) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____415 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}
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
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____632 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____670 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____708 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____767 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____811 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____867 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____903 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____937 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____985 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1029 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk:
  'Auu____1046 .
    'Auu____1046 ->
      FStar_Range.range -> 'Auu____1046 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1203 'Auu____1204 .
    ('Auu____1204 FStar_Pervasives_Native.option,'Auu____1203) FStar_ST.mref
      -> 'Auu____1204 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1499 = FStar_ST.op_Bang r in
      match uu____1499 with
      | FStar_Pervasives_Native.Some uu____1600 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1707 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1707 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___145_1715  ->
    match uu___145_1715 with
    | Arg (c,uu____1717,uu____1718) ->
        let uu____1719 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1719
    | MemoLazy uu____1720 -> "MemoLazy"
    | Abs (uu____1727,bs,uu____1729,uu____1730,uu____1731) ->
        let uu____1736 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1736
    | UnivArgs uu____1741 -> "UnivArgs"
    | Match uu____1748 -> "Match"
    | App (t,uu____1756,uu____1757) ->
        let uu____1758 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1758
    | Meta (m,uu____1760) -> "Meta"
    | Let uu____1761 -> "Let"
    | Steps (uu____1770,uu____1771,uu____1772) -> "Steps"
    | Debug t ->
        let uu____1782 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1782
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1791 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1791 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1809 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1809 then f () else ()
let is_empty: 'Auu____1815 . 'Auu____1815 Prims.list -> Prims.bool =
  fun uu___146_1821  ->
    match uu___146_1821 with | [] -> true | uu____1824 -> false
let lookup_bvar:
  'Auu____1833 .
    'Auu____1833 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1833
  =
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1852 ->
          let uu____1853 =
            let uu____1854 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1854 in
          failwith uu____1853
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
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____1899 =
            FStar_List.fold_left
              (fun uu____1925  ->
                 fun u1  ->
                   match uu____1925 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1950 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1950 with
                        | (k_u,n1) ->
                            let uu____1965 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1965
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1899 with
          | (uu____1983,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2008 = FStar_List.nth env x in
                 match uu____2008 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2012 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2021 ->
                   let uu____2022 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
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
                let uu____2053 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2053 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2070 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2070 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2078 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2086 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____2086 with
                                  | (uu____2091,m) -> n1 <= m)) in
                        if uu____2078 then rest1 else us1
                    | uu____2096 -> us1)
               | uu____2101 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2105 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2105 in
        let uu____2108 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____2108
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2110 = aux u in
           match uu____2110 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec closure_as_term:
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____2230  ->
             let uu____2231 = FStar_Syntax_Print.tag_of_term t in
             let uu____2232 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2231
               uu____2232);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2233 ->
             let t1 = FStar_Syntax_Subst.compress t in
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
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2282
                  then
                    let uu____2283 =
                      let uu____2284 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____2285 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____2284 uu____2285 in
                    failwith uu____2283
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____2288 =
                    let uu____2289 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____2289 in
                  mk uu____2288 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____2296 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2296
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____2298 = lookup_bvar env x in
                  (match uu____2298 with
                   | Univ uu____2299 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2303) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2391 = closures_as_binders_delayed cfg env bs in
                  (match uu____2391 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2425 =
                         let uu____2426 =
                           let uu____2443 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2443) in
                         FStar_Syntax_Syntax.Tm_abs uu____2426 in
                       mk uu____2425 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2474 = closures_as_binders_delayed cfg env bs in
                  (match uu____2474 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2522 =
                    let uu____2535 =
                      let uu____2542 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2542] in
                    closures_as_binders_delayed cfg env uu____2535 in
                  (match uu____2522 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2564 =
                         let uu____2565 =
                           let uu____2572 =
                             let uu____2573 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2573
                               FStar_Pervasives_Native.fst in
                           (uu____2572, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2565 in
                       mk uu____2564 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2664 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2664
                    | FStar_Util.Inr c ->
                        let uu____2678 = close_comp cfg env c in
                        FStar_Util.Inr uu____2678 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2694 =
                    let uu____2695 =
                      let uu____2722 = closure_as_term_delayed cfg env t11 in
                      (uu____2722, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2695 in
                  mk uu____2694 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2773 =
                    let uu____2774 =
                      let uu____2781 = closure_as_term_delayed cfg env t' in
                      let uu____2784 =
                        let uu____2785 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2785 in
                      (uu____2781, uu____2784) in
                    FStar_Syntax_Syntax.Tm_meta uu____2774 in
                  mk uu____2773 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2845 =
                    let uu____2846 =
                      let uu____2853 = closure_as_term_delayed cfg env t' in
                      let uu____2856 =
                        let uu____2857 =
                          let uu____2864 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2864) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2857 in
                      (uu____2853, uu____2856) in
                    FStar_Syntax_Syntax.Tm_meta uu____2846 in
                  mk uu____2845 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2883 =
                    let uu____2884 =
                      let uu____2891 = closure_as_term_delayed cfg env t' in
                      let uu____2894 =
                        let uu____2895 =
                          let uu____2904 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2904) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2895 in
                      (uu____2891, uu____2894) in
                    FStar_Syntax_Syntax.Tm_meta uu____2884 in
                  mk uu____2883 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2917 =
                    let uu____2918 =
                      let uu____2925 = closure_as_term_delayed cfg env t' in
                      (uu____2925, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2918 in
                  mk uu____2917 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2955  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2962 =
                    let uu____2973 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2973
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2992 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___163_2998 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___163_2998.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___163_2998.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2992)) in
                  (match uu____2962 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___164_3014 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___164_3014.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___164_3014.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3025,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3060  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____3067 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3067
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3075  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3085 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3085
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___165_3097 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___165_3097.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___165_3097.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___166_3098 = lb in
                    let uu____3099 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___166_3098.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___166_3098.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3099
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3117  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
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
                                                norm_pat env3 p1 in
                                              (match uu____3454 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3284 with
                               | (pats1,env3) ->
                                   ((let uu___167_3556 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___167_3556.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___168_3575 = x in
                                let uu____3576 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___168_3575.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___168_3575.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3576
                                } in
                              ((let uu___169_3584 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___169_3584.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___170_3589 = x in
                                let uu____3590 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___170_3589.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___170_3589.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3590
                                } in
                              ((let uu___171_3598 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___171_3598.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___172_3608 = x in
                                let uu____3609 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___172_3608.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___172_3608.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3609
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___173_3618 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___173_3618.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3621 = norm_pat env1 pat in
                        (match uu____3621 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3656 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3656 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3662 =
                    let uu____3663 =
                      let uu____3686 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3686) in
                    FStar_Syntax_Syntax.Tm_match uu____3663 in
                  mk uu____3662 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
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
and closures_as_args_delayed:
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
                     let uu____3830 = closure_as_term_delayed cfg env x in
                     (uu____3830, imp)) args
and closures_as_binders_delayed:
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
                          let uu___174_3984 = b in
                          let uu____3985 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___174_3984.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___174_3984.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3985
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3846 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
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
                 let uu____4081 = closure_as_term_delayed cfg env t in
                 let uu____4082 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4081 uu____4082
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4095 = closure_as_term_delayed cfg env t in
                 let uu____4096 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4095 uu____4096
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
                        (fun uu___147_4122  ->
                           match uu___147_4122 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4126 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4126
                           | f -> f)) in
                 let uu____4130 =
                   let uu___175_4131 = c1 in
                   let uu____4132 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4132;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___175_4131.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4130)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___148_4142  ->
            match uu___148_4142 with
            | FStar_Syntax_Syntax.DECREASES uu____4143 -> false
            | uu____4146 -> true))
and close_lcomp_opt:
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
                   (fun uu___149_4166  ->
                      match uu___149_4166 with
                      | FStar_Syntax_Syntax.DECREASES uu____4167 -> false
                      | uu____4170 -> true)) in
            let rc1 =
              let uu___176_4172 = rc in
              let uu____4173 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___176_4172.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4173;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4180 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4201 =
      let uu____4202 =
        let uu____4213 = FStar_Util.string_of_int i in
        (uu____4213, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4202 in
    const_as_tm uu____4201 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____4249 =
    match uu____4249 with
    | (a,uu____4257) ->
        let uu____4260 =
          let uu____4261 = FStar_Syntax_Subst.compress a in
          uu____4261.FStar_Syntax_Syntax.n in
        (match uu____4260 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4277 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4277
         | uu____4278 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4292 =
    match uu____4292 with
    | (a,uu____4304) ->
        let uu____4311 =
          let uu____4312 = FStar_Syntax_Subst.compress a in
          uu____4312.FStar_Syntax_Syntax.n in
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
               let uu____4371 = FStar_Util.int_of_string i in
               (fv1, uu____4371) in
             FStar_Pervasives_Native.Some uu____4366
         | uu____4376 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4390 =
    match uu____4390 with
    | (a,uu____4398) ->
        let uu____4401 =
          let uu____4402 = FStar_Syntax_Subst.compress a in
          uu____4402.FStar_Syntax_Syntax.n in
        (match uu____4401 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4408 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4418 =
    match uu____4418 with
    | (a,uu____4426) ->
        let uu____4429 =
          let uu____4430 = FStar_Syntax_Subst.compress a in
          uu____4430.FStar_Syntax_Syntax.n in
        (match uu____4429 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4436 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4446 =
    match uu____4446 with
    | (a,uu____4454) ->
        let uu____4457 =
          let uu____4458 = FStar_Syntax_Subst.compress a in
          uu____4458.FStar_Syntax_Syntax.n in
        (match uu____4457 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____4464)) ->
             FStar_Pervasives_Native.Some (FStar_Util.string_of_bytes bytes)
         | uu____4469 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4495 =
    match uu____4495 with
    | (a,uu____4509) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4538 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4555 = sequence xs in
              (match uu____4555 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4575 = FStar_Syntax_Util.list_elements a in
        (match uu____4575 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4593 =
               FStar_List.map
                 (fun x  ->
                    let uu____4603 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4603) elts in
             sequence uu____4593) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4641 = f a in FStar_Pervasives_Native.Some uu____4641
    | uu____4642 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4692 = f a0 a1 in FStar_Pervasives_Native.Some uu____4692
    | uu____4693 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4742 = FStar_List.map as_a args in lift_unary (f r) uu____4742 in
  let binary_op as_a f r args =
    let uu____4798 = FStar_List.map as_a args in lift_binary (f r) uu____4798 in
  let as_primitive_step uu____4822 =
    match uu____4822 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4870 = f x in int_as_const r uu____4870) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4898 = f x y in int_as_const r uu____4898) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4919 = f x in bool_as_const r uu____4919) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4947 = f x y in bool_as_const r uu____4947) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4975 = f x y in string_as_const r uu____4975) in
  let list_of_string' rng s =
    let name l =
      let uu____4989 =
        let uu____4990 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4990 in
      mk uu____4989 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5000 =
      let uu____5003 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5003 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5000 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____5078 = arg_as_string a1 in
        (match uu____5078 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5084 = arg_as_list arg_as_string a2 in
             (match uu____5084 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5097 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5097
              | uu____5098 -> FStar_Pervasives_Native.None)
         | uu____5103 -> FStar_Pervasives_Native.None)
    | uu____5106 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5120 = FStar_Util.string_of_int i in
    string_as_const rng uu____5120 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5136 = FStar_Util.string_of_int i in
    string_as_const rng uu____5136 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5166 args =
    match args with
    | uu____5178::(t,uu____5180)::[] ->
        let uu____5209 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5209
    | uu____5214 -> FStar_Pervasives_Native.None in
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
          (let uu___177_5300 = t in
           {
             FStar_Syntax_Syntax.n = (uu___177_5300.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___177_5300.FStar_Syntax_Syntax.vars)
           })
    | uu____5303 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
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
             let r1 =
               let uu____5448 = FStar_Range.mk_pos from_l from_c in
               let uu____5449 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5448 uu____5449 in
             let uu____5450 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5450
         | uu____5455 -> FStar_Pervasives_Native.None)
    | uu____5476 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5506)::(a1,uu____5508)::(a2,uu____5510)::[] ->
        let uu____5547 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5547 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5560 -> FStar_Pervasives_Native.None)
    | uu____5561 -> failwith "Unexpected number of arguments" in
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
                                                  "list_of_string"] in
                                              (uu____5892,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5899 =
                                              let uu____5914 =
                                                let uu____5927 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5927,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5936 =
                                                let uu____5951 =
                                                  let uu____5970 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5970,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5983 =
                                                  let uu____6004 =
                                                    let uu____6025 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6025,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6040 =
                                                    let uu____6063 =
                                                      let uu____6084 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6084,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6099 =
                                                      let uu____6122 =
                                                        let uu____6141 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6141,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6122] in
                                                    uu____6063 :: uu____6099 in
                                                  uu____6004 :: uu____6040 in
                                                uu____5951 :: uu____5983 in
                                              uu____5914 :: uu____5936 in
                                            uu____5879 :: uu____5899 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5864 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5849 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5834 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5819 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5804 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5789 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5774 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5759 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5744 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5729 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5714 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5699 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5684 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5669 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5654 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5639 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5624 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5609 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5594 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5579 in
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
      let uu____6748 =
        let uu____6749 =
          let uu____6750 = FStar_Syntax_Syntax.as_arg c in [uu____6750] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6749 in
      uu____6748 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6785 =
              let uu____6798 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6798, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6817  ->
                        fun uu____6818  ->
                          match (uu____6817, uu____6818) with
                          | ((int_to_t1,x),(uu____6837,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6847 =
              let uu____6862 =
                let uu____6875 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6875, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6894  ->
                          fun uu____6895  ->
                            match (uu____6894, uu____6895) with
                            | ((int_to_t1,x),(uu____6914,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6924 =
                let uu____6939 =
                  let uu____6952 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6952, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6971  ->
                            fun uu____6972  ->
                              match (uu____6971, uu____6972) with
                              | ((int_to_t1,x),(uu____6991,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6939] in
              uu____6862 :: uu____6924 in
            uu____6785 :: uu____6847)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7087)::(a1,uu____7089)::(a2,uu____7091)::[] ->
        let uu____7128 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7128 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___178_7134 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___178_7134.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___178_7134.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___179_7138 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___179_7138.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___179_7138.FStar_Syntax_Syntax.vars)
                })
         | uu____7139 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7141)::uu____7142::(a1,uu____7144)::(a2,uu____7146)::[] ->
        let uu____7195 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7195 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___178_7201 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___178_7201.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___178_7201.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___179_7205 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___179_7205.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___179_7205.FStar_Syntax_Syntax.vars)
                })
         | uu____7206 -> FStar_Pervasives_Native.None)
    | uu____7207 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      interpretation = interp_prop
    } in
  [propositional_equality; hetero_propositional_equality]
let reduce_primops:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____7220 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7220
      then tm
      else
        (let uu____7222 = FStar_Syntax_Util.head_and_args tm in
         match uu____7222 with
         | (head1,args) ->
             let uu____7259 =
               let uu____7260 = FStar_Syntax_Util.un_uinst head1 in
               uu____7260.FStar_Syntax_Syntax.n in
             (match uu____7259 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7264 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7264 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7277 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7277 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7281 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___180_7292 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___180_7292.tcenv);
           delta_level = (uu___180_7292.delta_level);
           primitive_steps = equality_ops
         }) tm
let maybe_simplify:
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      let steps = cfg.steps in
      let w t =
        let uu___181_7316 = t in
        {
          FStar_Syntax_Syntax.n = (uu___181_7316.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___181_7316.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7333 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7373 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
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
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7406
             then
               let uu____7407 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
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
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7742
                then
                  let uu____7743 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
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
                       FStar_Parser_Const.imp_lid in
                   if uu____8078
                   then
                     let uu____8079 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
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
                         let uu____8400 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8400
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8402 -> tm1
                   else
                     (let uu____8418 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8418
                      then
                        let uu____8419 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8419 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8474)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8513)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8552 -> tm1
                      else
                        (let uu____8568 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8568
                         then
                           match args with
                           | (t,uu____8570)::[] ->
                               let uu____8587 =
                                 let uu____8588 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8588.FStar_Syntax_Syntax.n in
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
                                   FStar_Syntax_Subst.compress t in
                                 uu____8667.FStar_Syntax_Syntax.n in
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
                                FStar_Parser_Const.exists_lid in
                            if uu____8713
                            then
                              match args with
                              | (t,uu____8715)::[] ->
                                  let uu____8732 =
                                    let uu____8733 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8733.FStar_Syntax_Syntax.n in
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
                                      FStar_Syntax_Subst.compress t in
                                    uu____8812.FStar_Syntax_Syntax.n in
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
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8882
             then
               let uu____8883 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
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
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9218
                then
                  let uu____9219 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
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
                       FStar_Parser_Const.imp_lid in
                   if uu____9554
                   then
                     let uu____9555 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
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
                         let uu____9876 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9876
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9878 -> tm1
                   else
                     (let uu____9894 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9894
                      then
                        let uu____9895 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9895 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9950)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9989)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10028 -> tm1
                      else
                        (let uu____10044 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10044
                         then
                           match args with
                           | (t,uu____10046)::[] ->
                               let uu____10063 =
                                 let uu____10064 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10064.FStar_Syntax_Syntax.n in
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
                                   FStar_Syntax_Subst.compress t in
                                 uu____10143.FStar_Syntax_Syntax.n in
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
                                FStar_Parser_Const.exists_lid in
                            if uu____10189
                            then
                              match args with
                              | (t,uu____10191)::[] ->
                                  let uu____10208 =
                                    let uu____10209 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10209.FStar_Syntax_Syntax.n in
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
                                      FStar_Syntax_Subst.compress t in
                                    uu____10288.FStar_Syntax_Syntax.n in
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
let is_norm_request:
  'Auu____10341 .
    FStar_Syntax_Syntax.term -> 'Auu____10341 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10354 =
        let uu____10361 =
          let uu____10362 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10362.FStar_Syntax_Syntax.n in
        (uu____10361, args) in
      match uu____10354 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10368::uu____10369::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10373::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10378::uu____10379::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10382 -> false
let get_norm_request:
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
            let uu____10438 = FStar_Syntax_Util.un_uinst s1 in
            uu____10438.FStar_Syntax_Syntax.n in
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
              let names2 = FStar_Syntax_Embeddings.unembed_string_list names1 in
              let lids =
                FStar_All.pipe_right names2
                  (FStar_List.map FStar_Ident.lid_of_str) in
              UnfoldOnly lids
          | uu____10489 -> failwith "Not an embedded `Prims.step`" in
        FStar_Syntax_Embeddings.unembed_list unembed_step s in
      match args with
      | uu____10496::(tm,uu____10498)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10521)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10536)::uu____10537::(tm,uu____10539)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10579 =
              let uu____10582 = full_norm steps in parse_steps uu____10582 in
            Beta :: uu____10579 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10591 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___150_10609  ->
    match uu___150_10609 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10612;
           FStar_Syntax_Syntax.vars = uu____10613;_},uu____10614,uu____10615))::uu____10616
        -> true
    | uu____10623 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          let firstn k l =
            if (FStar_List.length l) < k
            then (l, [])
            else FStar_Util.first_N k l in
          log cfg
            (fun uu____10758  ->
               let uu____10759 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10760 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10761 =
                 let uu____10762 =
                   let uu____10765 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10765 in
                 stack_to_string uu____10762 in
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
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10832 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10831 uu____10832 in
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
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___182_10902 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___182_10902.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___182_10902.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10935 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10935) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let uu____10942 =
                 get_norm_request
                   (norm
                      (let uu___183_10951 = cfg in
                       {
                         steps = (uu___183_10951.steps);
                         tcenv = (uu___183_10951.tcenv);
                         delta_level =
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.Delta_constant];
                         primitive_steps = (uu___183_10951.primitive_steps)
                       }) env []) args in
               (match uu____10942 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10961 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___151_10966  ->
                                match uu___151_10966 with
                                | UnfoldUntil uu____10967 -> true
                                | UnfoldOnly uu____10968 -> true
                                | uu____10971 -> false)) in
                      if uu____10961
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg' =
                      let uu___184_10976 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___184_10976.tcenv);
                        delta_level;
                        primitive_steps = (uu___184_10976.primitive_steps)
                      } in
                    let stack' = (Debug t1) ::
                      (Steps
                         ((cfg.steps), (cfg.primitive_steps),
                           (cfg.delta_level)))
                      :: stack1 in
                    norm cfg' env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10984;
                  FStar_Syntax_Syntax.vars = uu____10985;_},a1::a2::rest)
               ->
               let uu____11033 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11033 with
                | (hd1,uu____11049) ->
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
                    (FStar_Const.Const_reflect uu____11114);
                  FStar_Syntax_Syntax.pos = uu____11115;
                  FStar_Syntax_Syntax.vars = uu____11116;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11148 = FStar_List.tl stack1 in
               norm cfg env uu____11148 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11151;
                  FStar_Syntax_Syntax.vars = uu____11152;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11184 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11184 with
                | (reify_head,uu____11200) ->
                    let a1 =
                      let uu____11222 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11222 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11225);
                            FStar_Syntax_Syntax.pos = uu____11226;
                            FStar_Syntax_Syntax.vars = uu____11227;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11261 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11271 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11271
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11278 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11278
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11281 =
                      let uu____11288 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11288, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11281 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___152_11302  ->
                         match uu___152_11302 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11305 =
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
                 if uu____11305
                 then false
                 else
                   (let uu____11307 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___153_11314  ->
                              match uu___153_11314 with
                              | UnfoldOnly uu____11315 -> true
                              | uu____11318 -> false)) in
                    match uu____11307 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11322 -> should_delta) in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____11327 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____11327 in
                  let uu____11328 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____11328 with
                  | FStar_Pervasives_Native.None  ->
                      (log cfg
                         (fun uu____11341  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | FStar_Pervasives_Native.Some (us,t2) ->
                      (log cfg
                         (fun uu____11352  ->
                            let uu____11353 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____11354 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____11353 uu____11354);
                       (let t3 =
                          let uu____11356 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____11356
                          then t2
                          else
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid
                                 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                              t2 in
                        let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____11366))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____11389 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____11390 ->
                              let uu____11391 =
                                let uu____11392 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____11392 in
                              failwith uu____11391
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11395 = lookup_bvar env x in
               (match uu____11395 with
                | Univ uu____11396 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11421 = FStar_ST.op_Bang r in
                      (match uu____11421 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11502  ->
                                 let uu____11503 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11504 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11503
                                   uu____11504);
                            (let uu____11505 =
                               let uu____11506 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11506.FStar_Syntax_Syntax.n in
                             match uu____11505 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11509 ->
                                 norm cfg env2 stack1 t'
                             | uu____11526 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11578)::uu____11579 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11588)::uu____11589 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11599,uu____11600))::stack_rest ->
                    (match c with
                     | Univ uu____11604 -> norm cfg (c :: env) stack_rest t1
                     | uu____11605 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11610::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11626  ->
                                         let uu____11627 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11627);
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
                                           (fun uu___154_11632  ->
                                              match uu___154_11632 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11633 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11637  ->
                                         let uu____11638 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11638);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11639 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11642 ->
                                   let cfg1 =
                                     let uu___185_11646 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___185_11646.tcenv);
                                       delta_level =
                                         (uu___185_11646.delta_level);
                                       primitive_steps =
                                         (uu___185_11646.primitive_steps)
                                     } in
                                   let uu____11647 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11647)
                          | uu____11648::tl1 ->
                              (log cfg
                                 (fun uu____11667  ->
                                    let uu____11668 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11668);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___186_11698 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___186_11698.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11759  ->
                          let uu____11760 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11760);
                     norm cfg env stack2 t1)
                | (Debug uu____11761)::uu____11762 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11765 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11765
                    else
                      (let uu____11767 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11767 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11791  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11807 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11807
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11817 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11817)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_11822 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_11822.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_11822.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11823 -> lopt in
                           (log cfg
                              (fun uu____11829  ->
                                 let uu____11830 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11830);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___188_11843 = cfg in
                               let uu____11844 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___188_11843.steps);
                                 tcenv = (uu___188_11843.tcenv);
                                 delta_level = (uu___188_11843.delta_level);
                                 primitive_steps = uu____11844
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11853)::uu____11854 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11861 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11861
                    else
                      (let uu____11863 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11863 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11887  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11903 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11903
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11913 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11913)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_11918 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_11918.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_11918.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11919 -> lopt in
                           (log cfg
                              (fun uu____11925  ->
                                 let uu____11926 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11926);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___188_11939 = cfg in
                               let uu____11940 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___188_11939.steps);
                                 tcenv = (uu___188_11939.tcenv);
                                 delta_level = (uu___188_11939.delta_level);
                                 primitive_steps = uu____11940
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11949)::uu____11950 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11961 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11961
                    else
                      (let uu____11963 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11963 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11987  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12003 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12003
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12013 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12013)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_12018 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_12018.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_12018.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12019 -> lopt in
                           (log cfg
                              (fun uu____12025  ->
                                 let uu____12026 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12026);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___188_12039 = cfg in
                               let uu____12040 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___188_12039.steps);
                                 tcenv = (uu___188_12039.tcenv);
                                 delta_level = (uu___188_12039.delta_level);
                                 primitive_steps = uu____12040
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12049)::uu____12050 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12059 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12059
                    else
                      (let uu____12061 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12061 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12085  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12101 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12101
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12111 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12111)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_12116 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_12116.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_12116.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12117 -> lopt in
                           (log cfg
                              (fun uu____12123  ->
                                 let uu____12124 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12124);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___188_12137 = cfg in
                               let uu____12138 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___188_12137.steps);
                                 tcenv = (uu___188_12137.tcenv);
                                 delta_level = (uu___188_12137.delta_level);
                                 primitive_steps = uu____12138
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12147)::uu____12148 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12163 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12163
                    else
                      (let uu____12165 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12165 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12189  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12205 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12205
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12215 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12215)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_12220 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_12220.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_12220.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12221 -> lopt in
                           (log cfg
                              (fun uu____12227  ->
                                 let uu____12228 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12228);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___188_12241 = cfg in
                               let uu____12242 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___188_12241.steps);
                                 tcenv = (uu___188_12241.tcenv);
                                 delta_level = (uu___188_12241.delta_level);
                                 primitive_steps = uu____12242
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12251 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12251
                    else
                      (let uu____12253 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12253 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12277  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12293 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12293
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12303 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12303)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_12308 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_12308.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_12308.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12309 -> lopt in
                           (log cfg
                              (fun uu____12315  ->
                                 let uu____12316 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12316);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___188_12329 = cfg in
                               let uu____12330 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___188_12329.steps);
                                 tcenv = (uu___188_12329.tcenv);
                                 delta_level = (uu___188_12329.delta_level);
                                 primitive_steps = uu____12330
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____12377  ->
                         fun stack2  ->
                           match uu____12377 with
                           | (a,aq) ->
                               let uu____12389 =
                                 let uu____12390 =
                                   let uu____12397 =
                                     let uu____12398 =
                                       let uu____12417 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12417, false) in
                                     Clos uu____12398 in
                                   (uu____12397, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12390 in
                               uu____12389 :: stack2) args) in
               (log cfg
                  (fun uu____12469  ->
                     let uu____12470 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12470);
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
                             ((let uu___189_12494 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___189_12494.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___189_12494.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12495 ->
                      let uu____12500 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12500)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12503 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12503 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12528 =
                          let uu____12529 =
                            let uu____12536 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___190_12538 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___190_12538.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___190_12538.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12536) in
                          FStar_Syntax_Syntax.Tm_refine uu____12529 in
                        mk uu____12528 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12557 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12557
               else
                 (let uu____12559 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12559 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12567 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12579  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12567 c1 in
                      let t2 =
                        let uu____12589 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12589 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12648)::uu____12649 -> norm cfg env stack1 t11
                | (Arg uu____12658)::uu____12659 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12668;
                       FStar_Syntax_Syntax.vars = uu____12669;_},uu____12670,uu____12671))::uu____12672
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12679)::uu____12680 ->
                    norm cfg env stack1 t11
                | uu____12689 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12693  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12710 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12710
                        | FStar_Util.Inr c ->
                            let uu____12718 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12718 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12724 =
                        let uu____12725 =
                          let uu____12726 =
                            let uu____12753 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12753, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12726 in
                        mk uu____12725 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12724)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12829,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12830;
                               FStar_Syntax_Syntax.lbunivs = uu____12831;
                               FStar_Syntax_Syntax.lbtyp = uu____12832;
                               FStar_Syntax_Syntax.lbeff = uu____12833;
                               FStar_Syntax_Syntax.lbdef = uu____12834;_}::uu____12835),uu____12836)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12872 =
                 (let uu____12875 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12875) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12877 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12877))) in
               if uu____12872
               then
                 let env1 =
                   let uu____12881 =
                     let uu____12882 =
                       let uu____12901 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12901,
                         false) in
                     Clos uu____12882 in
                   uu____12881 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12953 =
                    let uu____12958 =
                      let uu____12959 =
                        let uu____12960 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12960
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12959] in
                    FStar_Syntax_Subst.open_term uu____12958 body in
                  match uu____12953 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____12974 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____12974 in
                        FStar_Util.Inl
                          (let uu___191_12984 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_12984.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_12984.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___192_12986 = lb in
                        let uu____12987 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___192_12986.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___192_12986.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____12987
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13004  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____13027 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13027 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13063 =
                               let uu___193_13064 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___193_13064.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___193_13064.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13063 in
                           let uu____13065 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13065 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13085 =
                                   FStar_List.map (fun uu____13089  -> Dummy)
                                     lbs1 in
                                 let uu____13090 =
                                   let uu____13093 =
                                     FStar_List.map
                                       (fun uu____13101  -> Dummy) xs1 in
                                   FStar_List.append uu____13093 env in
                                 FStar_List.append uu____13085 uu____13090 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13113 =
                                       let uu___194_13114 = rc in
                                       let uu____13115 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___194_13114.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13115;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___194_13114.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13113
                                 | uu____13122 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___195_13126 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___195_13126.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___195_13126.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13130 =
                        FStar_List.map (fun uu____13134  -> Dummy) lbs2 in
                      FStar_List.append uu____13130 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13136 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13136 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___196_13152 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___196_13152.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___196_13152.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13179 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13179
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13198 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13249  ->
                        match uu____13249 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13322 =
                                let uu___197_13323 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___197_13323.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___197_13323.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13322 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____13198 with
                | (rec_env,memos,uu____13451) ->
                    let uu____13480 =
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
                             let uu____13885 =
                               let uu____13886 =
                                 let uu____13905 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13905, false) in
                               Clos uu____13886 in
                             uu____13885 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
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
                             FStar_Syntax_Syntax.pos = uu____13973;
                             FStar_Syntax_Syntax.vars = uu____13974;_},uu____13975,uu____13976))::uu____13977
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____13984 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____13994 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____13994
                        then
                          let uu___198_13995 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___198_13995.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___198_13995.primitive_steps)
                          }
                        else
                          (let uu___199_13997 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___199_13997.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___199_13997.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____13999 =
                         let uu____14000 = FStar_Syntax_Subst.compress head1 in
                         uu____14000.FStar_Syntax_Syntax.n in
                       match uu____13999 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14018 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14018 with
                            | (uu____14019,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14025 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14033 =
                                         let uu____14034 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14034.FStar_Syntax_Syntax.n in
                                       match uu____14033 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14040,uu____14041))
                                           ->
                                           let uu____14050 =
                                             let uu____14051 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14051.FStar_Syntax_Syntax.n in
                                           (match uu____14050 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14057,msrc,uu____14059))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14068 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14068
                                            | uu____14069 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14070 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14071 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14071 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___200_14076 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___200_14076.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___200_14076.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___200_14076.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14077 =
                                            FStar_List.tl stack1 in
                                          let uu____14078 =
                                            let uu____14079 =
                                              let uu____14082 =
                                                let uu____14083 =
                                                  let uu____14096 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14096) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14083 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14082 in
                                            uu____14079
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14077
                                            uu____14078
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14112 =
                                            let uu____14113 = is_return body in
                                            match uu____14113 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14117;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14118;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14123 -> false in
                                          if uu____14112
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
                                               let uu____14147 =
                                                 let uu____14150 =
                                                   let uu____14151 =
                                                     let uu____14168 =
                                                       let uu____14171 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14171] in
                                                     (uu____14168, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14151 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14150 in
                                               uu____14147
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14187 =
                                                 let uu____14188 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14188.FStar_Syntax_Syntax.n in
                                               match uu____14187 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14194::uu____14195::[])
                                                   ->
                                                   let uu____14202 =
                                                     let uu____14205 =
                                                       let uu____14206 =
                                                         let uu____14213 =
                                                           let uu____14216 =
                                                             let uu____14217
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14217 in
                                                           let uu____14218 =
                                                             let uu____14221
                                                               =
                                                               let uu____14222
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14222 in
                                                             [uu____14221] in
                                                           uu____14216 ::
                                                             uu____14218 in
                                                         (bind1, uu____14213) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14206 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14205 in
                                                   uu____14202
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14230 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14236 =
                                                 let uu____14239 =
                                                   let uu____14240 =
                                                     let uu____14255 =
                                                       let uu____14258 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14259 =
                                                         let uu____14262 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14263 =
                                                           let uu____14266 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14267 =
                                                             let uu____14270
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14271
                                                               =
                                                               let uu____14274
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14275
                                                                 =
                                                                 let uu____14278
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14278] in
                                                               uu____14274 ::
                                                                 uu____14275 in
                                                             uu____14270 ::
                                                               uu____14271 in
                                                           uu____14266 ::
                                                             uu____14267 in
                                                         uu____14262 ::
                                                           uu____14263 in
                                                       uu____14258 ::
                                                         uu____14259 in
                                                     (bind_inst, uu____14255) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14240 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14239 in
                                               uu____14236
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14286 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14286 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14310 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14310 with
                            | (uu____14311,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14340 =
                                        let uu____14341 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14341.FStar_Syntax_Syntax.n in
                                      match uu____14340 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14347) -> t4
                                      | uu____14352 -> head2 in
                                    let uu____14353 =
                                      let uu____14354 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14354.FStar_Syntax_Syntax.n in
                                    match uu____14353 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14360 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14361 = maybe_extract_fv head2 in
                                  match uu____14361 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14371 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14371
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14376 =
                                          maybe_extract_fv head3 in
                                        match uu____14376 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14381 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14382 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14387 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14402 =
                                    match uu____14402 with
                                    | (e,q) ->
                                        let uu____14409 =
                                          let uu____14410 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14410.FStar_Syntax_Syntax.n in
                                        (match uu____14409 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14425 -> false) in
                                  let uu____14426 =
                                    let uu____14427 =
                                      let uu____14434 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14434 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14427 in
                                  if uu____14426
                                  then
                                    let uu____14439 =
                                      let uu____14440 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14440 in
                                    failwith uu____14439
                                  else ());
                                 (let uu____14442 =
                                    maybe_unfold_action head_app in
                                  match uu____14442 with
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
                                      let uu____14481 = FStar_List.tl stack1 in
                                      norm cfg env uu____14481 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14495 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14495 in
                           let uu____14496 = FStar_List.tl stack1 in
                           norm cfg env uu____14496 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14617  ->
                                     match uu____14617 with
                                     | (pat,wopt,tm) ->
                                         let uu____14665 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14665))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14697 = FStar_List.tl stack1 in
                           norm cfg env uu____14697 tm
                       | uu____14698 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14707;
                             FStar_Syntax_Syntax.vars = uu____14708;_},uu____14709,uu____14710))::uu____14711
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14718 -> false in
                    if should_reify
                    then
                      let uu____14719 = FStar_List.tl stack1 in
                      let uu____14720 =
                        let uu____14721 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14721 in
                      norm cfg env uu____14719 uu____14720
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14724 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14724
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___201_14733 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___201_14733.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___201_14733.primitive_steps)
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
                | uu____14735 ->
                    (match stack1 with
                     | uu____14736::uu____14737 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14742) ->
                              norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_alien (b,s) ->
                              norm cfg env
                                ((Meta (m, (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____14767 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14781 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14781
                           | uu____14792 -> m in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                             t1.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack1 t2)))
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
              let uu____14804 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14804 with
              | (uu____14805,return_repr) ->
                  let return_inst =
                    let uu____14814 =
                      let uu____14815 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14815.FStar_Syntax_Syntax.n in
                    match uu____14814 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14821::[]) ->
                        let uu____14828 =
                          let uu____14831 =
                            let uu____14832 =
                              let uu____14839 =
                                let uu____14842 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14842] in
                              (return_tm, uu____14839) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14832 in
                          FStar_Syntax_Syntax.mk uu____14831 in
                        uu____14828 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14850 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14853 =
                    let uu____14856 =
                      let uu____14857 =
                        let uu____14872 =
                          let uu____14875 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14876 =
                            let uu____14879 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14879] in
                          uu____14875 :: uu____14876 in
                        (return_inst, uu____14872) in
                      FStar_Syntax_Syntax.Tm_app uu____14857 in
                    FStar_Syntax_Syntax.mk uu____14856 in
                  uu____14853 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14888 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14888 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14891 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14891
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14892;
                     FStar_TypeChecker_Env.mtarget = uu____14893;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14894;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14905;
                     FStar_TypeChecker_Env.mtarget = uu____14906;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14907;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14925 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14925)
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
                (fun uu____14981  ->
                   match uu____14981 with
                   | (a,imp) ->
                       let uu____14992 = norm cfg env [] a in
                       (uu____14992, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___202_15009 = comp1 in
            let uu____15012 =
              let uu____15013 =
                let uu____15022 = norm cfg env [] t in
                let uu____15023 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15022, uu____15023) in
              FStar_Syntax_Syntax.Total uu____15013 in
            {
              FStar_Syntax_Syntax.n = uu____15012;
              FStar_Syntax_Syntax.pos =
                (uu___202_15009.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___202_15009.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___203_15038 = comp1 in
            let uu____15041 =
              let uu____15042 =
                let uu____15051 = norm cfg env [] t in
                let uu____15052 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15051, uu____15052) in
              FStar_Syntax_Syntax.GTotal uu____15042 in
            {
              FStar_Syntax_Syntax.n = uu____15041;
              FStar_Syntax_Syntax.pos =
                (uu___203_15038.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___203_15038.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15104  ->
                      match uu____15104 with
                      | (a,i) ->
                          let uu____15115 = norm cfg env [] a in
                          (uu____15115, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___155_15126  ->
                      match uu___155_15126 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15130 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15130
                      | f -> f)) in
            let uu___204_15134 = comp1 in
            let uu____15137 =
              let uu____15138 =
                let uu___205_15139 = ct in
                let uu____15140 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15141 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15144 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15140;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___205_15139.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15141;
                  FStar_Syntax_Syntax.effect_args = uu____15144;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15138 in
            {
              FStar_Syntax_Syntax.n = uu____15137;
              FStar_Syntax_Syntax.pos =
                (uu___204_15134.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___204_15134.FStar_Syntax_Syntax.vars)
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
            (let uu___206_15162 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___206_15162.tcenv);
               delta_level = (uu___206_15162.delta_level);
               primitive_steps = (uu___206_15162.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15167 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15167 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15170 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___207_15189 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___207_15189.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___207_15189.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15196 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15196
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
                    let uu___208_15207 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___208_15207.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___208_15207.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___208_15207.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___209_15209 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___209_15209.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___209_15209.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___209_15209.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___209_15209.FStar_Syntax_Syntax.flags)
                    } in
              let uu___210_15210 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___210_15210.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___210_15210.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15212 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15215  ->
        match uu____15215 with
        | (x,imp) ->
            let uu____15218 =
              let uu___211_15219 = x in
              let uu____15220 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___211_15219.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___211_15219.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15220
              } in
            (uu____15218, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15226 =
          FStar_List.fold_left
            (fun uu____15244  ->
               fun b  ->
                 match uu____15244 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15226 with | (nbs,uu____15272) -> FStar_List.rev nbs
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
            let uu____15288 =
              let uu___212_15289 = rc in
              let uu____15290 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___212_15289.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15290;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___212_15289.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15288
        | uu____15297 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          match stack1 with
          | [] -> t
          | (Debug tm)::stack2 ->
              ((let uu____15309 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15309
                then
                  let uu____15310 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15311 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____15310
                    uu____15311
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___213_15329 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___213_15329.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15398  ->
                    let uu____15399 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15399);
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
              let uu____15435 =
                let uu___214_15436 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___214_15436.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___214_15436.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15435
          | (Arg (Univ uu____15437,uu____15438,uu____15439))::uu____15440 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15443,uu____15444))::uu____15445 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15461),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15490  ->
                    let uu____15491 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15491);
               if FStar_List.contains (Exclude Iota) cfg.steps
               then
                 (if FStar_List.contains WHNF cfg.steps
                  then
                    let arg = closure_as_term cfg env1 tm in
                    let t1 =
                      FStar_Syntax_Syntax.extend_app t (arg, aq)
                        FStar_Pervasives_Native.None r in
                    rebuild cfg env1 stack2 t1
                  else
                    (let stack3 = (App (t, aq, r)) :: stack2 in
                     norm cfg env1 stack3 tm))
               else
                 (let uu____15501 = FStar_ST.op_Bang m in
                  match uu____15501 with
                  | FStar_Pervasives_Native.None  ->
                      if FStar_List.contains WHNF cfg.steps
                      then
                        let arg = closure_as_term cfg env1 tm in
                        let t1 =
                          FStar_Syntax_Syntax.extend_app t (arg, aq)
                            FStar_Pervasives_Native.None r in
                        rebuild cfg env1 stack2 t1
                      else
                        (let stack3 = (MemoLazy m) :: (App (t, aq, r)) ::
                           stack2 in
                         norm cfg env1 stack3 tm)
                  | FStar_Pervasives_Native.Some (uu____15601,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15625 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15625
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15635  ->
                    let uu____15636 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15636);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15641 =
                  log cfg
                    (fun uu____15646  ->
                       let uu____15647 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15648 =
                         let uu____15649 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15666  ->
                                   match uu____15666 with
                                   | (p,uu____15676,uu____15677) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15649
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15647 uu____15648);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___156_15694  ->
                               match uu___156_15694 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15695 -> false)) in
                     let steps' =
                       let uu____15699 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15699
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___215_15703 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___215_15703.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___215_15703.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15747 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15770 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15836  ->
                                   fun uu____15837  ->
                                     match (uu____15836, uu____15837) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15940 = norm_pat env3 p1 in
                                         (match uu____15940 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15770 with
                          | (pats1,env3) ->
                              ((let uu___216_16042 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___216_16042.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___217_16061 = x in
                           let uu____16062 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___217_16061.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___217_16061.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16062
                           } in
                         ((let uu___218_16070 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___218_16070.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___219_16075 = x in
                           let uu____16076 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___219_16075.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___219_16075.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16076
                           } in
                         ((let uu___220_16084 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___220_16084.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___221_16094 = x in
                           let uu____16095 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___221_16094.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___221_16094.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16095
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___222_16104 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___222_16104.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____16108 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16122 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16122 with
                                 | (p,wopt,e) ->
                                     let uu____16142 = norm_pat env1 p in
                                     (match uu____16142 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16173 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16173 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16179 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16179) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16189) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16194 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16195;
                        FStar_Syntax_Syntax.fv_delta = uu____16196;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16197;
                        FStar_Syntax_Syntax.fv_delta = uu____16198;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16199);_}
                      -> true
                  | uu____16206 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | FStar_Pervasives_Native.None  -> b
                  | FStar_Pervasives_Native.Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee_orig p =
                  let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                  let uu____16335 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16335 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16384 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16387 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16390 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16409 ->
                                let uu____16410 =
                                  let uu____16411 = is_cons head1 in
                                  Prims.op_Negation uu____16411 in
                                FStar_Util.Inr uu____16410)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16432 =
                             let uu____16433 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16433.FStar_Syntax_Syntax.n in
                           (match uu____16432 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16443 ->
                                let uu____16444 =
                                  let uu____16445 = is_cons head1 in
                                  Prims.op_Negation uu____16445 in
                                FStar_Util.Inr uu____16444))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16498)::rest_a,(p1,uu____16501)::rest_p) ->
                      let uu____16545 = matches_pat t1 p1 in
                      (match uu____16545 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16570 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16672 = matches_pat scrutinee1 p1 in
                      (match uu____16672 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16692  ->
                                 let uu____16693 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16694 =
                                   let uu____16695 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16695
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16693 uu____16694);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16712 =
                                        let uu____16713 =
                                          let uu____16732 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16732, false) in
                                        Clos uu____16713 in
                                      uu____16712 :: env2) env1 s in
                             let uu____16785 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16785))) in
                let uu____16786 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16786
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___157_16809  ->
                match uu___157_16809 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16813 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16819 -> d in
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
            let uu___223_16848 = config s e in
            {
              steps = (uu___223_16848.steps);
              tcenv = (uu___223_16848.tcenv);
              delta_level = (uu___223_16848.delta_level);
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
      fun t  -> let uu____16873 = config s e in norm_comp uu____16873 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16882 = config [] env in norm_universe uu____16882 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16891 = config [] env in ghost_to_pure_aux uu____16891 [] c
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
        let uu____16905 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16905 in
      let uu____16906 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16906
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___224_16908 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___224_16908.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___224_16908.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16911  ->
                    let uu____16912 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16912))
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
            ((let uu____16931 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16931);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____16944 = config [AllowUnboundUniverses] env in
          norm_comp uu____16944 [] c
        with
        | e ->
            ((let uu____16951 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16951);
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
                   let uu____16991 =
                     let uu____16992 =
                       let uu____16999 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____16999) in
                     FStar_Syntax_Syntax.Tm_refine uu____16992 in
                   mk uu____16991 t01.FStar_Syntax_Syntax.pos
               | uu____17004 -> t2)
          | uu____17005 -> t2 in
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
        let uu____17057 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17057 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17086 ->
                 let uu____17093 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17093 with
                  | (actuals,uu____17103,uu____17104) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17118 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17118 with
                         | (binders,args) ->
                             let uu____17135 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17135
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
      | uu____17145 ->
          let uu____17146 = FStar_Syntax_Util.head_and_args t in
          (match uu____17146 with
           | (head1,args) ->
               let uu____17183 =
                 let uu____17184 = FStar_Syntax_Subst.compress head1 in
                 uu____17184.FStar_Syntax_Syntax.n in
               (match uu____17183 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17187,thead) ->
                    let uu____17213 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17213 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17255 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___229_17263 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___229_17263.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___229_17263.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___229_17263.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___229_17263.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___229_17263.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___229_17263.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___229_17263.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___229_17263.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___229_17263.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___229_17263.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___229_17263.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___229_17263.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___229_17263.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___229_17263.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___229_17263.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___229_17263.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___229_17263.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___229_17263.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___229_17263.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___229_17263.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___229_17263.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___229_17263.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___229_17263.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___229_17263.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___229_17263.FStar_TypeChecker_Env.identifier_info)
                                 }) t in
                            match uu____17255 with
                            | (uu____17264,ty,uu____17266) ->
                                eta_expand_with_type env t ty))
                | uu____17267 ->
                    let uu____17268 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___230_17276 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___230_17276.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___230_17276.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___230_17276.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___230_17276.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___230_17276.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___230_17276.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___230_17276.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___230_17276.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___230_17276.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___230_17276.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___230_17276.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___230_17276.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___230_17276.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___230_17276.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___230_17276.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___230_17276.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___230_17276.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___230_17276.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___230_17276.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___230_17276.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___230_17276.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___230_17276.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___230_17276.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___230_17276.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___230_17276.FStar_TypeChecker_Env.identifier_info)
                         }) t in
                    (match uu____17268 with
                     | (uu____17277,ty,uu____17279) ->
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
            | (uu____17357,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17363,FStar_Util.Inl t) ->
                let uu____17369 =
                  let uu____17372 =
                    let uu____17373 =
                      let uu____17386 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17386) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17373 in
                  FStar_Syntax_Syntax.mk uu____17372 in
                uu____17369 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17390 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17390 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17417 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17472 ->
                    let uu____17473 =
                      let uu____17482 =
                        let uu____17483 = FStar_Syntax_Subst.compress t3 in
                        uu____17483.FStar_Syntax_Syntax.n in
                      (uu____17482, tc) in
                    (match uu____17473 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17508) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17545) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17584,FStar_Util.Inl uu____17585) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17608 -> failwith "Impossible") in
              (match uu____17417 with
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
          let uu____17717 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17717 with
          | (univ_names1,binders1,tc) ->
              let uu____17775 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17775)
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
          let uu____17814 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17814 with
          | (univ_names1,binders1,tc) ->
              let uu____17874 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17874)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17909 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17909 with
           | (univ_names1,binders1,typ1) ->
               let uu___231_17937 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___231_17937.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___231_17937.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___231_17937.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___231_17937.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___232_17958 = s in
          let uu____17959 =
            let uu____17960 =
              let uu____17969 = FStar_List.map (elim_uvars env) sigs in
              (uu____17969, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____17960 in
          {
            FStar_Syntax_Syntax.sigel = uu____17959;
            FStar_Syntax_Syntax.sigrng =
              (uu___232_17958.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___232_17958.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___232_17958.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___232_17958.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____17986 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____17986 with
           | (univ_names1,uu____18004,typ1) ->
               let uu___233_18018 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___233_18018.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___233_18018.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___233_18018.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___233_18018.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18024 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18024 with
           | (univ_names1,uu____18042,typ1) ->
               let uu___234_18056 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___234_18056.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___234_18056.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___234_18056.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___234_18056.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18090 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18090 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18113 =
                            let uu____18114 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18114 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18113 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___235_18117 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___235_18117.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___235_18117.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___236_18118 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___236_18118.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___236_18118.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___236_18118.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___236_18118.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___237_18130 = s in
          let uu____18131 =
            let uu____18132 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18132 in
          {
            FStar_Syntax_Syntax.sigel = uu____18131;
            FStar_Syntax_Syntax.sigrng =
              (uu___237_18130.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___237_18130.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___237_18130.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___237_18130.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18136 = elim_uvars_aux_t env us [] t in
          (match uu____18136 with
           | (us1,uu____18154,t1) ->
               let uu___238_18168 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___238_18168.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___238_18168.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___238_18168.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___238_18168.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18169 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18171 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18171 with
           | (univs1,binders,signature) ->
               let uu____18199 =
                 let uu____18208 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18208 with
                 | (univs_opening,univs2) ->
                     let uu____18235 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18235) in
               (match uu____18199 with
                | (univs_opening,univs_closing) ->
                    let uu____18252 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18258 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18259 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18258, uu____18259) in
                    (match uu____18252 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18281 =
                           match uu____18281 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18299 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18299 with
                                | (us1,t1) ->
                                    let uu____18310 =
                                      let uu____18315 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18322 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18315, uu____18322) in
                                    (match uu____18310 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18335 =
                                           let uu____18340 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18349 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18340, uu____18349) in
                                         (match uu____18335 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18365 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18365 in
                                              let uu____18366 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18366 with
                                               | (uu____18387,uu____18388,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18403 =
                                                       let uu____18404 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18404 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18403 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18409 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18409 with
                           | (uu____18422,uu____18423,t1) -> t1 in
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
                             | uu____18483 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18500 =
                               let uu____18501 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18501.FStar_Syntax_Syntax.n in
                             match uu____18500 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18560 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18589 =
                               let uu____18590 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18590.FStar_Syntax_Syntax.n in
                             match uu____18589 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18611) ->
                                 let uu____18632 = destruct_action_body body in
                                 (match uu____18632 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18677 ->
                                 let uu____18678 = destruct_action_body t in
                                 (match uu____18678 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18727 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18727 with
                           | (action_univs,t) ->
                               let uu____18736 = destruct_action_typ_templ t in
                               (match uu____18736 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___239_18777 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___239_18777.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___239_18777.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___240_18779 = ed in
                           let uu____18780 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18781 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18782 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18783 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18784 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18785 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18786 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18787 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18788 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18789 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18790 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18791 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18792 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18793 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___240_18779.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___240_18779.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18780;
                             FStar_Syntax_Syntax.bind_wp = uu____18781;
                             FStar_Syntax_Syntax.if_then_else = uu____18782;
                             FStar_Syntax_Syntax.ite_wp = uu____18783;
                             FStar_Syntax_Syntax.stronger = uu____18784;
                             FStar_Syntax_Syntax.close_wp = uu____18785;
                             FStar_Syntax_Syntax.assert_p = uu____18786;
                             FStar_Syntax_Syntax.assume_p = uu____18787;
                             FStar_Syntax_Syntax.null_wp = uu____18788;
                             FStar_Syntax_Syntax.trivial = uu____18789;
                             FStar_Syntax_Syntax.repr = uu____18790;
                             FStar_Syntax_Syntax.return_repr = uu____18791;
                             FStar_Syntax_Syntax.bind_repr = uu____18792;
                             FStar_Syntax_Syntax.actions = uu____18793
                           } in
                         let uu___241_18796 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___241_18796.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___241_18796.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___241_18796.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___241_18796.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___158_18813 =
            match uu___158_18813 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18840 = elim_uvars_aux_t env us [] t in
                (match uu____18840 with
                 | (us1,uu____18864,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___242_18883 = sub_eff in
            let uu____18884 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18887 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___242_18883.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___242_18883.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18884;
              FStar_Syntax_Syntax.lift = uu____18887
            } in
          let uu___243_18890 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___243_18890.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___243_18890.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___243_18890.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___243_18890.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18900 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18900 with
           | (univ_names1,binders1,comp1) ->
               let uu___244_18934 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___244_18934.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___244_18934.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___244_18934.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___244_18934.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18945 -> s