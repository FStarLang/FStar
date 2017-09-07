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
  fun uu___148_390  ->
    match uu___148_390 with
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
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____636 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____674 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____712 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____771 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____815 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____871 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____907 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____941 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____989 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps,primitive_step Prims.list,FStar_TypeChecker_Env.delta_level
                                       Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1037 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk:
  'Auu____1066 .
    'Auu____1066 ->
      FStar_Range.range -> 'Auu____1066 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo:
  'Auu____1223 'Auu____1224 .
    ('Auu____1224 FStar_Pervasives_Native.option,'Auu____1223) FStar_ST.mref
      -> 'Auu____1224 -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uu____1519 = FStar_ST.op_Bang r in
      match uu____1519 with
      | FStar_Pervasives_Native.Some uu____1620 ->
          failwith "Unexpected set_memo: thunk already evaluated"
      | FStar_Pervasives_Native.None  ->
          FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1727 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1727 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___149_1735  ->
    match uu___149_1735 with
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
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1812 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1812 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1830 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1830 then f () else ()
let is_empty: 'Auu____1836 . 'Auu____1836 Prims.list -> Prims.bool =
  fun uu___150_1842  ->
    match uu___150_1842 with | [] -> true | uu____1845 -> false
let lookup_bvar:
  'Auu____1854 .
    'Auu____1854 Prims.list -> FStar_Syntax_Syntax.bv -> 'Auu____1854
  =
  fun env  ->
    fun x  ->
      try FStar_List.nth env x.FStar_Syntax_Syntax.index
      with
      | uu____1873 ->
          let uu____1874 =
            let uu____1875 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1875 in
          failwith uu____1874
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
          let uu____1920 =
            FStar_List.fold_left
              (fun uu____1946  ->
                 fun u1  ->
                   match uu____1946 with
                   | (cur_kernel,cur_max,out) ->
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
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2029 = FStar_List.nth env x in
                 match uu____2029 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2033 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2042 ->
                   let uu____2043 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____2043
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
                let uu____2074 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____2074 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____2091 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____2091 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2099 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
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
          (fun uu____2251  ->
             let uu____2252 = FStar_Syntax_Print.tag_of_term t in
             let uu____2253 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____2252
               uu____2253);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____2254 ->
             let t1 = FStar_Syntax_Subst.compress t in
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
                      (FStar_List.contains CheckNoUvars) in
                  if uu____2303
                  then
                    let uu____2304 =
                      let uu____2305 =
                        FStar_Range.string_of_range
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
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____2324) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
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
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
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
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
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
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2976  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
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
                           (let uu___169_3019 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___169_3019.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___169_3019.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3013)) in
                  (match uu____2983 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___170_3035 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___170_3035.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___170_3035.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3046,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
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
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____3106 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____3106
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___171_3118 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___171_3118.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___171_3118.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_43  -> FStar_Util.Inl _0_43)) in
                    let uu___172_3119 = lb in
                    let uu____3120 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___172_3119.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___172_3119.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3120
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____3138  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____3217 =
                    match uu____3217 with
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
                                              let uu____3475 =
                                                norm_pat env3 p1 in
                                              (match uu____3475 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3305 with
                               | (pats1,env3) ->
                                   ((let uu___173_3577 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___173_3577.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___174_3596 = x in
                                let uu____3597 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___174_3596.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___174_3596.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3597
                                } in
                              ((let uu___175_3605 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___175_3605.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___176_3610 = x in
                                let uu____3611 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___176_3610.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___176_3610.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3611
                                } in
                              ((let uu___177_3619 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___177_3619.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___178_3629 = x in
                                let uu____3630 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___178_3629.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___178_3629.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3630
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___179_3639 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___179_3639.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3642 = norm_pat env1 pat in
                        (match uu____3642 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
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
        | uu____3789 -> closure_as_term cfg env t
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
        | uu____3813 ->
            FStar_List.map
              (fun uu____3832  ->
                 match uu____3832 with
                 | (x,imp) ->
                     let uu____3851 = closure_as_term_delayed cfg env x in
                     (uu____3851, imp)) args
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
        let uu____3867 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3922  ->
                  fun uu____3923  ->
                    match (uu____3922, uu____3923) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___180_4005 = b in
                          let uu____4006 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___180_4005.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___180_4005.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4006
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3867 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____4087 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4102 = closure_as_term_delayed cfg env t in
                 let uu____4103 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4102 uu____4103
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4116 = closure_as_term_delayed cfg env t in
                 let uu____4117 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4116 uu____4117
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
                        (fun uu___151_4143  ->
                           match uu___151_4143 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4147 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____4147
                           | f -> f)) in
                 let uu____4151 =
                   let uu___181_4152 = c1 in
                   let uu____4153 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4153;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___181_4152.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4151)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___152_4163  ->
            match uu___152_4163 with
            | FStar_Syntax_Syntax.DECREASES uu____4164 -> false
            | uu____4167 -> true))
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
                   (fun uu___153_4187  ->
                      match uu___153_4187 with
                      | FStar_Syntax_Syntax.DECREASES uu____4188 -> false
                      | uu____4191 -> true)) in
            let rc1 =
              let uu___182_4193 = rc in
              let uu____4194 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___182_4193.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4194;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4201 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____4222 =
      let uu____4223 =
        let uu____4234 = FStar_Util.string_of_int i in
        (uu____4234, FStar_Pervasives_Native.None) in
      FStar_Const.Const_int uu____4223 in
    const_as_tm uu____4222 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b = const_as_tm (FStar_Const.Const_string (b, p)) p in
  let arg_as_int uu____4268 =
    match uu____4268 with
    | (a,uu____4276) ->
        let uu____4279 =
          let uu____4280 = FStar_Syntax_Subst.compress a in
          uu____4280.FStar_Syntax_Syntax.n in
        (match uu____4279 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (i,FStar_Pervasives_Native.None )) ->
             let uu____4296 = FStar_Util.int_of_string i in
             FStar_Pervasives_Native.Some uu____4296
         | uu____4297 -> FStar_Pervasives_Native.None) in
  let arg_as_bounded_int uu____4311 =
    match uu____4311 with
    | (a,uu____4323) ->
        let uu____4330 =
          let uu____4331 = FStar_Syntax_Subst.compress a in
          uu____4331.FStar_Syntax_Syntax.n in
        (match uu____4330 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4341;
                FStar_Syntax_Syntax.vars = uu____4342;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4344;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4345;_},uu____4346)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4385 =
               let uu____4390 = FStar_Util.int_of_string i in
               (fv1, uu____4390) in
             FStar_Pervasives_Native.Some uu____4385
         | uu____4395 -> FStar_Pervasives_Native.None) in
  let arg_as_bool uu____4409 =
    match uu____4409 with
    | (a,uu____4417) ->
        let uu____4420 =
          let uu____4421 = FStar_Syntax_Subst.compress a in
          uu____4421.FStar_Syntax_Syntax.n in
        (match uu____4420 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             FStar_Pervasives_Native.Some b
         | uu____4427 -> FStar_Pervasives_Native.None) in
  let arg_as_char uu____4437 =
    match uu____4437 with
    | (a,uu____4445) ->
        let uu____4448 =
          let uu____4449 = FStar_Syntax_Subst.compress a in
          uu____4449.FStar_Syntax_Syntax.n in
        (match uu____4448 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             FStar_Pervasives_Native.Some c
         | uu____4455 -> FStar_Pervasives_Native.None) in
  let arg_as_string uu____4465 =
    match uu____4465 with
    | (a,uu____4473) ->
        let uu____4476 =
          let uu____4477 = FStar_Syntax_Subst.compress a in
          uu____4477.FStar_Syntax_Syntax.n in
        (match uu____4476 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____4483)) -> FStar_Pervasives_Native.Some s
         | uu____4484 -> FStar_Pervasives_Native.None) in
  let arg_as_list f uu____4510 =
    match uu____4510 with
    | (a,uu____4524) ->
        let rec sequence l =
          match l with
          | [] -> FStar_Pervasives_Native.Some []
          | (FStar_Pervasives_Native.None )::uu____4553 ->
              FStar_Pervasives_Native.None
          | (FStar_Pervasives_Native.Some x)::xs ->
              let uu____4570 = sequence xs in
              (match uu____4570 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some xs' ->
                   FStar_Pervasives_Native.Some (x :: xs')) in
        let uu____4590 = FStar_Syntax_Util.list_elements a in
        (match uu____4590 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some elts ->
             let uu____4608 =
               FStar_List.map
                 (fun x  ->
                    let uu____4618 = FStar_Syntax_Syntax.as_arg x in
                    f uu____4618) elts in
             sequence uu____4608) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4656 = f a in FStar_Pervasives_Native.Some uu____4656
    | uu____4657 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4707 = f a0 a1 in FStar_Pervasives_Native.Some uu____4707
    | uu____4708 -> FStar_Pervasives_Native.None in
  let unary_op as_a f r args =
    let uu____4757 = FStar_List.map as_a args in lift_unary (f r) uu____4757 in
  let binary_op as_a f r args =
    let uu____4813 = FStar_List.map as_a args in lift_binary (f r) uu____4813 in
  let as_primitive_step uu____4837 =
    match uu____4837 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____4885 = f x in int_as_const r uu____4885) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4913 = f x y in int_as_const r uu____4913) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____4934 = f x in bool_as_const r uu____4934) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4962 = f x y in bool_as_const r uu____4962) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____4990 = f x y in string_as_const r uu____4990) in
  let list_of_string' rng s =
    let name l =
      let uu____5004 =
        let uu____5005 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5005 in
      mk uu____5004 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5015 =
      let uu____5018 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5018 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5015 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____5093 = arg_as_string a1 in
        (match uu____5093 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5099 = arg_as_list arg_as_string a2 in
             (match uu____5099 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5112 = string_as_const rng r in
                  FStar_Pervasives_Native.Some uu____5112
              | uu____5113 -> FStar_Pervasives_Native.None)
         | uu____5118 -> FStar_Pervasives_Native.None)
    | uu____5121 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____5135 = FStar_Util.string_of_int i in
    string_as_const rng uu____5135 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____5151 = FStar_Util.string_of_int i in
    string_as_const rng uu____5151 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let range_of1 uu____5181 args =
    match args with
    | uu____5193::(t,uu____5195)::[] ->
        let uu____5224 = term_of_range t.FStar_Syntax_Syntax.pos in
        FStar_Pervasives_Native.Some uu____5224
    | uu____5229 -> FStar_Pervasives_Native.None in
  let set_range_of1 r args =
    match args with
    | uu____5267::(t,uu____5269)::({
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_range r1);
                                     FStar_Syntax_Syntax.pos = uu____5271;
                                     FStar_Syntax_Syntax.vars = uu____5272;_},uu____5273)::[]
        ->
        FStar_Pervasives_Native.Some
          (let uu___183_5315 = t in
           {
             FStar_Syntax_Syntax.n = (uu___183_5315.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r1;
             FStar_Syntax_Syntax.vars =
               (uu___183_5315.FStar_Syntax_Syntax.vars)
           })
    | uu____5318 -> FStar_Pervasives_Native.None in
  let mk_range1 r args =
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
             let r1 =
               let uu____5463 = FStar_Range.mk_pos from_l from_c in
               let uu____5464 = FStar_Range.mk_pos to_l to_c in
               FStar_Range.mk_range fn1 uu____5463 uu____5464 in
             let uu____5465 = term_of_range r1 in
             FStar_Pervasives_Native.Some uu____5465
         | uu____5470 -> FStar_Pervasives_Native.None)
    | uu____5491 -> FStar_Pervasives_Native.None in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____5521)::(a1,uu____5523)::(a2,uu____5525)::[] ->
        let uu____5562 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____5562 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____5575 -> FStar_Pervasives_Native.None)
    | uu____5576 -> failwith "Unexpected number of arguments" in
  let basic_ops =
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
                                            let uu____5894 =
                                              let uu____5907 =
                                                FStar_Parser_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "list_of_string"] in
                                              (uu____5907,
                                                (Prims.parse_int "1"),
                                                (unary_op arg_as_string
                                                   list_of_string')) in
                                            let uu____5914 =
                                              let uu____5929 =
                                                let uu____5942 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "string_of_list"] in
                                                (uu____5942,
                                                  (Prims.parse_int "1"),
                                                  (unary_op
                                                     (arg_as_list arg_as_char)
                                                     string_of_list')) in
                                              let uu____5951 =
                                                let uu____5966 =
                                                  let uu____5985 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "concat"] in
                                                  (uu____5985,
                                                    (Prims.parse_int "2"),
                                                    string_concat') in
                                                let uu____5998 =
                                                  let uu____6019 =
                                                    let uu____6040 =
                                                      FStar_Parser_Const.p2l
                                                        ["Prims"; "range_of"] in
                                                    (uu____6040,
                                                      (Prims.parse_int "2"),
                                                      range_of1) in
                                                  let uu____6055 =
                                                    let uu____6078 =
                                                      let uu____6099 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "set_range_of"] in
                                                      (uu____6099,
                                                        (Prims.parse_int "3"),
                                                        set_range_of1) in
                                                    let uu____6114 =
                                                      let uu____6137 =
                                                        let uu____6156 =
                                                          FStar_Parser_Const.p2l
                                                            ["Prims";
                                                            "mk_range"] in
                                                        (uu____6156,
                                                          (Prims.parse_int
                                                             "5"), mk_range1) in
                                                      [uu____6137] in
                                                    uu____6078 :: uu____6114 in
                                                  uu____6019 :: uu____6055 in
                                                uu____5966 :: uu____5998 in
                                              uu____5929 :: uu____5951 in
                                            uu____5894 :: uu____5914 in
                                          (FStar_Parser_Const.op_notEq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq true)) ::
                                            uu____5879 in
                                        (FStar_Parser_Const.op_Eq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq false)) :: uu____5864 in
                                      (FStar_Parser_Const.string_compare,
                                        (Prims.parse_int "2"),
                                        (binary_op arg_as_string
                                           string_compare'))
                                        :: uu____5849 in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_bool string_of_bool2))
                                      :: uu____5834 in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_int string_of_int2)) ::
                                    uu____5819 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5804 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5789 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5774 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5759 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5744 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____5729 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____5714 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____5699 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____5684 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____5669 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____5654 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____5639 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____5624 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____5609 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____5594 in
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
      let uu____6763 =
        let uu____6764 =
          let uu____6765 = FStar_Syntax_Syntax.as_arg c in [uu____6765] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6764 in
      uu____6763 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6800 =
              let uu____6813 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6813, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____6832  ->
                        fun uu____6833  ->
                          match (uu____6832, uu____6833) with
                          | ((int_to_t1,x),(uu____6852,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____6862 =
              let uu____6877 =
                let uu____6890 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6890, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____6909  ->
                          fun uu____6910  ->
                            match (uu____6909, uu____6910) with
                            | ((int_to_t1,x),(uu____6929,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____6939 =
                let uu____6954 =
                  let uu____6967 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6967, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____6986  ->
                            fun uu____6987  ->
                              match (uu____6986, uu____6987) with
                              | ((int_to_t1,x),(uu____7006,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____6954] in
              uu____6877 :: uu____6939 in
            uu____6800 :: uu____6862)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____7102)::(a1,uu____7104)::(a2,uu____7106)::[] ->
        let uu____7143 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7143 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___184_7149 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_7149.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_7149.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___185_7153 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___185_7153.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___185_7153.FStar_Syntax_Syntax.vars)
                })
         | uu____7154 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7156)::uu____7157::(a1,uu____7159)::(a2,uu____7161)::[] ->
        let uu____7210 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____7210 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___184_7216 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_7216.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_7216.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___185_7220 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___185_7220.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___185_7220.FStar_Syntax_Syntax.vars)
                })
         | uu____7221 -> FStar_Pervasives_Native.None)
    | uu____7222 -> failwith "Unexpected number of arguments" in
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
      let uu____7235 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____7235
      then tm
      else
        (let uu____7237 = FStar_Syntax_Util.head_and_args tm in
         match uu____7237 with
         | (head1,args) ->
             let uu____7274 =
               let uu____7275 = FStar_Syntax_Util.un_uinst head1 in
               uu____7275.FStar_Syntax_Syntax.n in
             (match uu____7274 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____7279 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____7279 with
                   | FStar_Pervasives_Native.None  -> tm
                   | FStar_Pervasives_Native.Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____7292 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____7292 with
                          | FStar_Pervasives_Native.None  -> tm
                          | FStar_Pervasives_Native.Some reduced -> reduced))
              | uu____7296 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___186_7307 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___186_7307.tcenv);
           delta_level = (uu___186_7307.delta_level);
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
        let uu___187_7331 = t in
        {
          FStar_Syntax_Syntax.n = (uu___187_7331.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___187_7331.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____7348 -> FStar_Pervasives_Native.None in
      let simplify arg = ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____7388 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____7388
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____7391;
                     FStar_Syntax_Syntax.vars = uu____7392;_},uu____7393);
                FStar_Syntax_Syntax.pos = uu____7394;
                FStar_Syntax_Syntax.vars = uu____7395;_},args)
             ->
             let uu____7421 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____7421
             then
               let uu____7422 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____7422 with
                | (FStar_Pervasives_Native.Some (true ),uu____7477)::
                    (uu____7478,(arg,uu____7480))::[] -> arg
                | (uu____7545,(arg,uu____7547))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____7548)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____7613)::uu____7614::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7677::(FStar_Pervasives_Native.Some (false
                               ),uu____7678)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____7741 -> tm1)
             else
               (let uu____7757 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____7757
                then
                  let uu____7758 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7758 with
                  | (FStar_Pervasives_Native.Some (true ),uu____7813)::uu____7814::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____7877::(FStar_Pervasives_Native.Some (true
                                 ),uu____7878)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7941)::
                      (uu____7942,(arg,uu____7944))::[] -> arg
                  | (uu____8009,(arg,uu____8011))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____8012)::[]
                      -> arg
                  | uu____8077 -> tm1
                else
                  (let uu____8093 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____8093
                   then
                     let uu____8094 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8094 with
                     | uu____8149::(FStar_Pervasives_Native.Some (true
                                    ),uu____8150)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8213)::uu____8214::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8277)::
                         (uu____8278,(arg,uu____8280))::[] -> arg
                     | (uu____8345,(p,uu____8347))::(uu____8348,(q,uu____8350))::[]
                         ->
                         let uu____8415 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8415
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____8417 -> tm1
                   else
                     (let uu____8433 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8433
                      then
                        let uu____8434 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8434 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8489)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8528)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8567 -> tm1
                      else
                        (let uu____8583 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8583
                         then
                           match args with
                           | (t,uu____8585)::[] ->
                               let uu____8602 =
                                 let uu____8603 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8603.FStar_Syntax_Syntax.n in
                               (match uu____8602 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8606::[],body,uu____8608) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8635 -> tm1)
                                | uu____8638 -> tm1)
                           | (uu____8639,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8640))::
                               (t,uu____8642)::[] ->
                               let uu____8681 =
                                 let uu____8682 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8682.FStar_Syntax_Syntax.n in
                               (match uu____8681 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8685::[],body,uu____8687) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____8714 -> tm1)
                                | uu____8717 -> tm1)
                           | uu____8718 -> tm1
                         else
                           (let uu____8728 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8728
                            then
                              match args with
                              | (t,uu____8730)::[] ->
                                  let uu____8747 =
                                    let uu____8748 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8748.FStar_Syntax_Syntax.n in
                                  (match uu____8747 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8751::[],body,uu____8753) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8780 -> tm1)
                                   | uu____8783 -> tm1)
                              | (uu____8784,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8785))::
                                  (t,uu____8787)::[] ->
                                  let uu____8826 =
                                    let uu____8827 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8827.FStar_Syntax_Syntax.n in
                                  (match uu____8826 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8830::[],body,uu____8832) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____8859 -> tm1)
                                   | uu____8862 -> tm1)
                              | uu____8863 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.pos = uu____8874;
                FStar_Syntax_Syntax.vars = uu____8875;_},args)
             ->
             let uu____8897 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
             if uu____8897
             then
               let uu____8898 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____8898 with
                | (FStar_Pervasives_Native.Some (true ),uu____8953)::
                    (uu____8954,(arg,uu____8956))::[] -> arg
                | (uu____9021,(arg,uu____9023))::(FStar_Pervasives_Native.Some
                                                  (true ),uu____9024)::[]
                    -> arg
                | (FStar_Pervasives_Native.Some (false ),uu____9089)::uu____9090::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9153::(FStar_Pervasives_Native.Some (false
                               ),uu____9154)::[]
                    -> w FStar_Syntax_Util.t_false
                | uu____9217 -> tm1)
             else
               (let uu____9233 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
                if uu____9233
                then
                  let uu____9234 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____9234 with
                  | (FStar_Pervasives_Native.Some (true ),uu____9289)::uu____9290::[]
                      -> w FStar_Syntax_Util.t_true
                  | uu____9353::(FStar_Pervasives_Native.Some (true
                                 ),uu____9354)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____9417)::
                      (uu____9418,(arg,uu____9420))::[] -> arg
                  | (uu____9485,(arg,uu____9487))::(FStar_Pervasives_Native.Some
                                                    (false ),uu____9488)::[]
                      -> arg
                  | uu____9553 -> tm1
                else
                  (let uu____9569 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.imp_lid in
                   if uu____9569
                   then
                     let uu____9570 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____9570 with
                     | uu____9625::(FStar_Pervasives_Native.Some (true
                                    ),uu____9626)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____9689)::uu____9690::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____9753)::
                         (uu____9754,(arg,uu____9756))::[] -> arg
                     | (uu____9821,(p,uu____9823))::(uu____9824,(q,uu____9826))::[]
                         ->
                         let uu____9891 = FStar_Syntax_Util.term_eq p q in
                         (if uu____9891
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____9893 -> tm1
                   else
                     (let uu____9909 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____9909
                      then
                        let uu____9910 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____9910 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9965)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____10004)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____10043 -> tm1
                      else
                        (let uu____10059 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____10059
                         then
                           match args with
                           | (t,uu____10061)::[] ->
                               let uu____10078 =
                                 let uu____10079 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10079.FStar_Syntax_Syntax.n in
                               (match uu____10078 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10082::[],body,uu____10084) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10111 -> tm1)
                                | uu____10114 -> tm1)
                           | (uu____10115,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10116))::
                               (t,uu____10118)::[] ->
                               let uu____10157 =
                                 let uu____10158 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____10158.FStar_Syntax_Syntax.n in
                               (match uu____10157 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____10161::[],body,uu____10163) ->
                                    (match simp_t body with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____10190 -> tm1)
                                | uu____10193 -> tm1)
                           | uu____10194 -> tm1
                         else
                           (let uu____10204 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____10204
                            then
                              match args with
                              | (t,uu____10206)::[] ->
                                  let uu____10223 =
                                    let uu____10224 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10224.FStar_Syntax_Syntax.n in
                                  (match uu____10223 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10227::[],body,uu____10229) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10256 -> tm1)
                                   | uu____10259 -> tm1)
                              | (uu____10260,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10261))::
                                  (t,uu____10263)::[] ->
                                  let uu____10302 =
                                    let uu____10303 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____10303.FStar_Syntax_Syntax.n in
                                  (match uu____10302 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____10306::[],body,uu____10308) ->
                                       (match simp_t body with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____10335 -> tm1)
                                   | uu____10338 -> tm1)
                              | uu____10339 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____10349 -> tm1)
let is_norm_request:
  'Auu____10356 .
    FStar_Syntax_Syntax.term -> 'Auu____10356 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10369 =
        let uu____10376 =
          let uu____10377 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10377.FStar_Syntax_Syntax.n in
        (uu____10376, args) in
      match uu____10369 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10383::uu____10384::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10388::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10393::uu____10394::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10397 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___154_10409  ->
    match uu___154_10409 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.WHNF  -> [WHNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10415 =
          let uu____10418 =
            let uu____10419 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10419 in
          [uu____10418] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10415
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10438 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10438) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10476 =
          FStar_Syntax_Embeddings.unembed_list
            FStar_Syntax_Embeddings.unembed_norm_step s in
        FStar_All.pipe_left tr_norm_steps uu____10476 in
      match args with
      | uu____10489::(tm,uu____10491)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10514)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10529)::uu____10530::(tm,uu____10532)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10572 =
              let uu____10575 = full_norm steps in parse_steps uu____10575 in
            Beta :: uu____10572 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10584 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___155_10602  ->
    match uu___155_10602 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.pos = uu____10605;
           FStar_Syntax_Syntax.vars = uu____10606;_},uu____10607,uu____10608))::uu____10609
        -> true
    | uu____10616 -> false
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
            (fun uu____10751  ->
               let uu____10752 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____10753 = FStar_Syntax_Print.term_to_string t1 in
               let uu____10754 =
                 let uu____10755 =
                   let uu____10758 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10758 in
                 stack_to_string uu____10755 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____10752
                 uu____10753 uu____10754);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____10781 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____10806 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____10823 =
                 let uu____10824 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____10825 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____10824 uu____10825 in
               failwith uu____10823
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____10826 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____10843 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____10844 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10845;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10846;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10849;
                 FStar_Syntax_Syntax.fv_delta = uu____10850;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10851;
                 FStar_Syntax_Syntax.fv_delta = uu____10852;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10853);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___188_10895 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___188_10895.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___188_10895.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____10928 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____10928) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___189_10936 = cfg in
                 let uu____10937 =
                   FStar_List.filter
                     (fun uu___156_10940  ->
                        match uu___156_10940 with
                        | UnfoldOnly uu____10941 -> false
                        | NoDeltaSteps  -> false
                        | uu____10944 -> true) cfg.steps in
                 {
                   steps = uu____10937;
                   tcenv = (uu___189_10936.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___189_10936.primitive_steps)
                 } in
               let uu____10945 = get_norm_request (norm cfg' env []) args in
               (match uu____10945 with
                | (s,tm) ->
                    let delta_level =
                      let uu____10961 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___157_10966  ->
                                match uu___157_10966 with
                                | UnfoldUntil uu____10967 -> true
                                | UnfoldOnly uu____10968 -> true
                                | uu____10971 -> false)) in
                      if uu____10961
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___190_10976 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___190_10976.tcenv);
                        delta_level;
                        primitive_steps = (uu___190_10976.primitive_steps)
                      } in
                    let stack' =
                      let tail1 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let uu____10987 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____10987
                      then
                        let uu____10990 =
                          let uu____10991 =
                            let uu____10996 = FStar_Util.now () in
                            (t1, uu____10996) in
                          Debug uu____10991 in
                        uu____10990 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____10998;
                  FStar_Syntax_Syntax.vars = uu____10999;_},a1::a2::rest)
               ->
               let uu____11047 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11047 with
                | (hd1,uu____11063) ->
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
                    (FStar_Const.Const_reflect uu____11128);
                  FStar_Syntax_Syntax.pos = uu____11129;
                  FStar_Syntax_Syntax.vars = uu____11130;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____11162 = FStar_List.tl stack1 in
               norm cfg env uu____11162 (FStar_Pervasives_Native.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.pos = uu____11165;
                  FStar_Syntax_Syntax.vars = uu____11166;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____11198 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____11198 with
                | (reify_head,uu____11214) ->
                    let a1 =
                      let uu____11236 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (FStar_Pervasives_Native.fst a) in
                      FStar_Syntax_Subst.compress uu____11236 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____11239);
                            FStar_Syntax_Syntax.pos = uu____11240;
                            FStar_Syntax_Syntax.vars = uu____11241;_},a2::[])
                         ->
                         norm cfg env stack1 (FStar_Pervasives_Native.fst a2)
                     | uu____11275 ->
                         let stack2 =
                           (App
                              (reify_head, FStar_Pervasives_Native.None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11285 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____11285
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11292 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11292
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____11295 =
                      let uu____11302 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11302, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11295 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___158_11316  ->
                         match uu___158_11316 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11319 =
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
                 if uu____11319
                 then false
                 else
                   (let uu____11321 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___159_11328  ->
                              match uu___159_11328 with
                              | UnfoldOnly uu____11329 -> true
                              | uu____11332 -> false)) in
                    match uu____11321 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11336 -> should_delta) in
               (log cfg
                  (fun uu____11344  ->
                     let uu____11345 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11346 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11347 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11345 uu____11346 uu____11347);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack1 t1
                else
                  (let r_env =
                     let uu____11350 = FStar_Syntax_Syntax.range_of_fv f in
                     FStar_TypeChecker_Env.set_range cfg.tcenv uu____11350 in
                   let uu____11351 =
                     FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                       r_env
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   match uu____11351 with
                   | FStar_Pervasives_Native.None  ->
                       (log cfg
                          (fun uu____11364  ->
                             FStar_Util.print "Tm_fvar case 2\n" []);
                        rebuild cfg env stack1 t1)
                   | FStar_Pervasives_Native.Some (us,t2) ->
                       (log cfg
                          (fun uu____11375  ->
                             let uu____11376 =
                               FStar_Syntax_Print.term_to_string t0 in
                             let uu____11377 =
                               FStar_Syntax_Print.term_to_string t2 in
                             FStar_Util.print2 ">>> Unfolded %s to %s\n"
                               uu____11376 uu____11377);
                        (let t3 =
                           let uu____11379 =
                             FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  (UnfoldUntil
                                     FStar_Syntax_Syntax.Delta_constant)) in
                           if uu____11379
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
                           | (UnivArgs (us',uu____11389))::stack2 ->
                               let env1 =
                                 FStar_All.pipe_right us'
                                   (FStar_List.fold_left
                                      (fun env1  ->
                                         fun u  -> (Univ u) :: env1) env) in
                               norm cfg env1 stack2 t3
                           | uu____11412 when
                               FStar_All.pipe_right cfg.steps
                                 (FStar_List.contains EraseUniverses)
                               -> norm cfg env stack1 t3
                           | uu____11413 ->
                               let uu____11414 =
                                 let uu____11415 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   uu____11415 in
                               failwith uu____11414
                         else norm cfg env stack1 t3))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11418 = lookup_bvar env x in
               (match uu____11418 with
                | Univ uu____11419 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11444 = FStar_ST.op_Bang r in
                      (match uu____11444 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11525  ->
                                 let uu____11526 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11527 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11526
                                   uu____11527);
                            (let uu____11528 =
                               let uu____11529 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11529.FStar_Syntax_Syntax.n in
                             match uu____11528 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11532 ->
                                 norm cfg env2 stack1 t'
                             | uu____11549 -> rebuild cfg env2 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____11601)::uu____11602 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11611)::uu____11612 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11622,uu____11623))::stack_rest ->
                    (match c with
                     | Univ uu____11627 -> norm cfg (c :: env) stack_rest t1
                     | uu____11628 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____11633::[] ->
                              (match lopt with
                               | FStar_Pervasives_Native.None  when
                                   FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____11649  ->
                                         let uu____11650 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11650);
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
                                           (fun uu___160_11655  ->
                                              match uu___160_11655 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____11656 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____11660  ->
                                         let uu____11661 =
                                           closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____11661);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____11662 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____11665 ->
                                   let cfg1 =
                                     let uu___191_11669 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___191_11669.tcenv);
                                       delta_level =
                                         (uu___191_11669.delta_level);
                                       primitive_steps =
                                         (uu___191_11669.primitive_steps)
                                     } in
                                   let uu____11670 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____11670)
                          | uu____11671::tl1 ->
                              (log cfg
                                 (fun uu____11690  ->
                                    let uu____11691 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11691);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___192_11721 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___192_11721.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____11782  ->
                          let uu____11783 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11783);
                     norm cfg env stack2 t1)
                | (Debug uu____11784)::uu____11785 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11792 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11792
                    else
                      (let uu____11794 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11794 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11818  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11834 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11834
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11844 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11844)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___193_11849 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___193_11849.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___193_11849.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11850 -> lopt in
                           (log cfg
                              (fun uu____11856  ->
                                 let uu____11857 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11857);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___194_11870 = cfg in
                               let uu____11871 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___194_11870.steps);
                                 tcenv = (uu___194_11870.tcenv);
                                 delta_level = (uu___194_11870.delta_level);
                                 primitive_steps = uu____11871
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11880)::uu____11881 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11888 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11888
                    else
                      (let uu____11890 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11890 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11914  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11930 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11930
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11940 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11940)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___193_11945 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___193_11945.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___193_11945.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11946 -> lopt in
                           (log cfg
                              (fun uu____11952  ->
                                 let uu____11953 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11953);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___194_11966 = cfg in
                               let uu____11967 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___194_11966.steps);
                                 tcenv = (uu___194_11966.tcenv);
                                 delta_level = (uu___194_11966.delta_level);
                                 primitive_steps = uu____11967
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11976)::uu____11977 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____11988 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____11988
                    else
                      (let uu____11990 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11990 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12014  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12030 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12030
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12040 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12040)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___193_12045 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___193_12045.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___193_12045.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12046 -> lopt in
                           (log cfg
                              (fun uu____12052  ->
                                 let uu____12053 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12053);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___194_12066 = cfg in
                               let uu____12067 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___194_12066.steps);
                                 tcenv = (uu___194_12066.tcenv);
                                 delta_level = (uu___194_12066.delta_level);
                                 primitive_steps = uu____12067
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____12076)::uu____12077 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12086 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12086
                    else
                      (let uu____12088 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12088 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12112  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12128 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12128
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12138 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12138)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___193_12143 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___193_12143.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___193_12143.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12144 -> lopt in
                           (log cfg
                              (fun uu____12150  ->
                                 let uu____12151 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12151);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___194_12164 = cfg in
                               let uu____12165 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___194_12164.steps);
                                 tcenv = (uu___194_12164.tcenv);
                                 delta_level = (uu___194_12164.delta_level);
                                 primitive_steps = uu____12165
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____12174)::uu____12175 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12190 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12190
                    else
                      (let uu____12192 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12192 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12216  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12232 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12232
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12242 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12242)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___193_12247 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___193_12247.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___193_12247.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12248 -> lopt in
                           (log cfg
                              (fun uu____12254  ->
                                 let uu____12255 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12255);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___194_12268 = cfg in
                               let uu____12269 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___194_12268.steps);
                                 tcenv = (uu___194_12268.tcenv);
                                 delta_level = (uu___194_12268.delta_level);
                                 primitive_steps = uu____12269
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____12278 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12278
                    else
                      (let uu____12280 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12280 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12304  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12320 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12320
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12330 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12330)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___193_12335 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___193_12335.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___193_12335.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12336 -> lopt in
                           (log cfg
                              (fun uu____12342  ->
                                 let uu____12343 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12343);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___194_12356 = cfg in
                               let uu____12357 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___194_12356.steps);
                                 tcenv = (uu___194_12356.tcenv);
                                 delta_level = (uu___194_12356.delta_level);
                                 primitive_steps = uu____12357
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
                      (fun uu____12404  ->
                         fun stack2  ->
                           match uu____12404 with
                           | (a,aq) ->
                               let uu____12416 =
                                 let uu____12417 =
                                   let uu____12424 =
                                     let uu____12425 =
                                       let uu____12444 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12444, false) in
                                     Clos uu____12425 in
                                   (uu____12424, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12417 in
                               uu____12416 :: stack2) args) in
               (log cfg
                  (fun uu____12496  ->
                     let uu____12497 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12497);
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
                             ((let uu___195_12521 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___195_12521.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___195_12521.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____12522 ->
                      let uu____12527 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____12527)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12530 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12530 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____12555 =
                          let uu____12556 =
                            let uu____12563 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___196_12565 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___196_12565.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___196_12565.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12563) in
                          FStar_Syntax_Syntax.Tm_refine uu____12556 in
                        mk uu____12555 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____12584 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____12584
               else
                 (let uu____12586 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12586 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12594 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12606  -> Dummy :: env1) env) in
                        norm_comp cfg uu____12594 c1 in
                      let t2 =
                        let uu____12616 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12616 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12675)::uu____12676 -> norm cfg env stack1 t11
                | (Arg uu____12685)::uu____12686 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12695;
                       FStar_Syntax_Syntax.vars = uu____12696;_},uu____12697,uu____12698))::uu____12699
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____12706)::uu____12707 ->
                    norm cfg env stack1 t11
                | uu____12716 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____12720  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____12737 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____12737
                        | FStar_Util.Inr c ->
                            let uu____12745 = norm_comp cfg env c in
                            FStar_Util.Inr uu____12745 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____12751 =
                        let uu____12752 =
                          let uu____12753 =
                            let uu____12780 = FStar_Syntax_Util.unascribe t12 in
                            (uu____12780, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____12753 in
                        mk uu____12752 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____12751)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12856,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12857;
                               FStar_Syntax_Syntax.lbunivs = uu____12858;
                               FStar_Syntax_Syntax.lbtyp = uu____12859;
                               FStar_Syntax_Syntax.lbeff = uu____12860;
                               FStar_Syntax_Syntax.lbdef = uu____12861;_}::uu____12862),uu____12863)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____12899 =
                 (let uu____12902 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____12902) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____12904 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____12904))) in
               if uu____12899
               then
                 let env1 =
                   let uu____12908 =
                     let uu____12909 =
                       let uu____12928 =
                         FStar_Util.mk_ref FStar_Pervasives_Native.None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12928,
                         false) in
                     Clos uu____12909 in
                   uu____12908 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____12980 =
                    let uu____12985 =
                      let uu____12986 =
                        let uu____12987 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____12987
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____12986] in
                    FStar_Syntax_Subst.open_term uu____12985 body in
                  match uu____12980 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____13001 = FStar_List.hd bs in
                          FStar_Pervasives_Native.fst uu____13001 in
                        FStar_Util.Inl
                          (let uu___197_13011 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___197_13011.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___197_13011.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___198_13013 = lb in
                        let uu____13014 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___198_13013.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___198_13013.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____13014
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____13031  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____13054 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13054 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13090 =
                               let uu___199_13091 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___199_13091.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___199_13091.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13090 in
                           let uu____13092 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13092 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13112 =
                                   FStar_List.map (fun uu____13116  -> Dummy)
                                     lbs1 in
                                 let uu____13117 =
                                   let uu____13120 =
                                     FStar_List.map
                                       (fun uu____13128  -> Dummy) xs1 in
                                   FStar_List.append uu____13120 env in
                                 FStar_List.append uu____13112 uu____13117 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13140 =
                                       let uu___200_13141 = rc in
                                       let uu____13142 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___200_13141.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13142;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___200_13141.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13140
                                 | uu____13149 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___201_13153 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___201_13153.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___201_13153.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13157 =
                        FStar_List.map (fun uu____13161  -> Dummy) lbs2 in
                      FStar_List.append uu____13157 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13163 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13163 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___202_13179 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___202_13179.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___202_13179.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13206 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____13206
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13225 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13276  ->
                        match uu____13276 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____13349 =
                                let uu___203_13350 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___203_13350.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___203_13350.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____13349 in
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
               (match uu____13225 with
                | (rec_env,memos,uu____13478) ->
                    let uu____13507 =
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
                             let uu____13912 =
                               let uu____13913 =
                                 let uu____13932 =
                                   FStar_Util.mk_ref
                                     FStar_Pervasives_Native.None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____13932, false) in
                               Clos uu____13913 in
                             uu____13912 :: env1)
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
                             FStar_Syntax_Syntax.pos = uu____14000;
                             FStar_Syntax_Syntax.vars = uu____14001;_},uu____14002,uu____14003))::uu____14004
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14011 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____14021 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____14021
                        then
                          let uu___204_14022 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___204_14022.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps =
                              (uu___204_14022.primitive_steps)
                          }
                        else
                          (let uu___205_14024 = cfg in
                           {
                             steps =
                               (FStar_List.append [Exclude Zeta] cfg.steps);
                             tcenv = (uu___205_14024.tcenv);
                             delta_level = (uu___205_14024.delta_level);
                             primitive_steps =
                               (uu___205_14024.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____14026 =
                         let uu____14027 = FStar_Syntax_Subst.compress head1 in
                         uu____14027.FStar_Syntax_Syntax.n in
                       match uu____14026 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14045 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14045 with
                            | (uu____14046,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____14052 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____14060 =
                                         let uu____14061 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____14061.FStar_Syntax_Syntax.n in
                                       match uu____14060 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____14067,uu____14068))
                                           ->
                                           let uu____14077 =
                                             let uu____14078 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____14078.FStar_Syntax_Syntax.n in
                                           (match uu____14077 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____14084,msrc,uu____14086))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____14095 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14095
                                            | uu____14096 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____14097 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____14098 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____14098 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___206_14103 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___206_14103.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___206_14103.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___206_14103.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____14104 =
                                            FStar_List.tl stack1 in
                                          let uu____14105 =
                                            let uu____14106 =
                                              let uu____14109 =
                                                let uu____14110 =
                                                  let uu____14123 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____14123) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____14110 in
                                              FStar_Syntax_Syntax.mk
                                                uu____14109 in
                                            uu____14106
                                              FStar_Pervasives_Native.None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____14104
                                            uu____14105
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____14139 =
                                            let uu____14140 = is_return body in
                                            match uu____14140 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____14144;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____14145;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____14150 -> false in
                                          if uu____14139
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
                                               let uu____14174 =
                                                 let uu____14177 =
                                                   let uu____14178 =
                                                     let uu____14195 =
                                                       let uu____14198 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____14198] in
                                                     (uu____14195, body1,
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____14178 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14177 in
                                               uu____14174
                                                 FStar_Pervasives_Native.None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____14214 =
                                                 let uu____14215 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____14215.FStar_Syntax_Syntax.n in
                                               match uu____14214 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____14221::uu____14222::[])
                                                   ->
                                                   let uu____14229 =
                                                     let uu____14232 =
                                                       let uu____14233 =
                                                         let uu____14240 =
                                                           let uu____14243 =
                                                             let uu____14244
                                                               =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____14244 in
                                                           let uu____14245 =
                                                             let uu____14248
                                                               =
                                                               let uu____14249
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____14249 in
                                                             [uu____14248] in
                                                           uu____14243 ::
                                                             uu____14245 in
                                                         (bind1, uu____14240) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____14233 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____14232 in
                                                   uu____14229
                                                     FStar_Pervasives_Native.None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____14257 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____14263 =
                                                 let uu____14266 =
                                                   let uu____14267 =
                                                     let uu____14282 =
                                                       let uu____14285 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____14286 =
                                                         let uu____14289 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____14290 =
                                                           let uu____14293 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____14294 =
                                                             let uu____14297
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____14298
                                                               =
                                                               let uu____14301
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____14302
                                                                 =
                                                                 let uu____14305
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____14305] in
                                                               uu____14301 ::
                                                                 uu____14302 in
                                                             uu____14297 ::
                                                               uu____14298 in
                                                           uu____14293 ::
                                                             uu____14294 in
                                                         uu____14289 ::
                                                           uu____14290 in
                                                       uu____14285 ::
                                                         uu____14286 in
                                                     (bind_inst, uu____14282) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14267 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14266 in
                                               uu____14263
                                                 FStar_Pervasives_Native.None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____14313 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____14313 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____14337 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____14337 with
                            | (uu____14338,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____14367 =
                                        let uu____14368 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____14368.FStar_Syntax_Syntax.n in
                                      match uu____14367 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____14374) -> t4
                                      | uu____14379 -> head2 in
                                    let uu____14380 =
                                      let uu____14381 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____14381.FStar_Syntax_Syntax.n in
                                    match uu____14380 with
                                    | FStar_Syntax_Syntax.Tm_fvar x ->
                                        FStar_Pervasives_Native.Some x
                                    | uu____14387 ->
                                        FStar_Pervasives_Native.None in
                                  let uu____14388 = maybe_extract_fv head2 in
                                  match uu____14388 with
                                  | FStar_Pervasives_Native.Some x when
                                      let uu____14398 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____14398
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____14403 =
                                          maybe_extract_fv head3 in
                                        match uu____14403 with
                                        | FStar_Pervasives_Native.Some
                                            uu____14408 ->
                                            FStar_Pervasives_Native.Some true
                                        | uu____14409 ->
                                            FStar_Pervasives_Native.Some
                                              false in
                                      (head3, action_unfolded)
                                  | uu____14414 ->
                                      (head2, FStar_Pervasives_Native.None) in
                                ((let is_arg_impure uu____14429 =
                                    match uu____14429 with
                                    | (e,q) ->
                                        let uu____14436 =
                                          let uu____14437 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____14437.FStar_Syntax_Syntax.n in
                                        (match uu____14436 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____14452 -> false) in
                                  let uu____14453 =
                                    let uu____14454 =
                                      let uu____14461 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____14461 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____14454 in
                                  if uu____14453
                                  then
                                    let uu____14466 =
                                      let uu____14467 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____14467 in
                                    failwith uu____14466
                                  else ());
                                 (let uu____14469 =
                                    maybe_unfold_action head_app in
                                  match uu____14469 with
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
                                      let uu____14508 = FStar_List.tl stack1 in
                                      norm cfg env uu____14508 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____14522 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____14522 in
                           let uu____14523 = FStar_List.tl stack1 in
                           norm cfg env uu____14523 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____14644  ->
                                     match uu____14644 with
                                     | (pat,wopt,tm) ->
                                         let uu____14692 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____14692))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____14724 = FStar_List.tl stack1 in
                           norm cfg env uu____14724 tm
                       | uu____14725 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.pos = uu____14734;
                             FStar_Syntax_Syntax.vars = uu____14735;_},uu____14736,uu____14737))::uu____14738
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____14745 -> false in
                    if should_reify
                    then
                      let uu____14746 = FStar_List.tl stack1 in
                      let uu____14747 =
                        let uu____14748 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____14748 in
                      norm cfg env uu____14746 uu____14747
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____14751 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____14751
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___207_14760 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___207_14760.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___207_14760.primitive_steps)
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
                | uu____14762 ->
                    (match stack1 with
                     | uu____14763::uu____14764 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled
                              (l,r,uu____14769) ->
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
                          | uu____14794 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____14808 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____14808
                           | uu____14819 -> m in
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
              let uu____14831 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____14831 with
              | (uu____14832,return_repr) ->
                  let return_inst =
                    let uu____14841 =
                      let uu____14842 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____14842.FStar_Syntax_Syntax.n in
                    match uu____14841 with
                    | FStar_Syntax_Syntax.Tm_uinst
                        (return_tm,uu____14848::[]) ->
                        let uu____14855 =
                          let uu____14858 =
                            let uu____14859 =
                              let uu____14866 =
                                let uu____14869 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____14869] in
                              (return_tm, uu____14866) in
                            FStar_Syntax_Syntax.Tm_uinst uu____14859 in
                          FStar_Syntax_Syntax.mk uu____14858 in
                        uu____14855 FStar_Pervasives_Native.None
                          e.FStar_Syntax_Syntax.pos
                    | uu____14877 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____14880 =
                    let uu____14883 =
                      let uu____14884 =
                        let uu____14899 =
                          let uu____14902 = FStar_Syntax_Syntax.as_arg t in
                          let uu____14903 =
                            let uu____14906 = FStar_Syntax_Syntax.as_arg e in
                            [uu____14906] in
                          uu____14902 :: uu____14903 in
                        (return_inst, uu____14899) in
                      FStar_Syntax_Syntax.Tm_app uu____14884 in
                    FStar_Syntax_Syntax.mk uu____14883 in
                  uu____14880 FStar_Pervasives_Native.None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____14915 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____14915 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14918 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____14918
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14919;
                     FStar_TypeChecker_Env.mtarget = uu____14920;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14921;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14932;
                     FStar_TypeChecker_Env.mtarget = uu____14933;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14934;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14952 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____14952)
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
                (fun uu____15008  ->
                   match uu____15008 with
                   | (a,imp) ->
                       let uu____15019 = norm cfg env [] a in
                       (uu____15019, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___208_15036 = comp1 in
            let uu____15039 =
              let uu____15040 =
                let uu____15049 = norm cfg env [] t in
                let uu____15050 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15049, uu____15050) in
              FStar_Syntax_Syntax.Total uu____15040 in
            {
              FStar_Syntax_Syntax.n = uu____15039;
              FStar_Syntax_Syntax.pos =
                (uu___208_15036.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___208_15036.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___209_15065 = comp1 in
            let uu____15068 =
              let uu____15069 =
                let uu____15078 = norm cfg env [] t in
                let uu____15079 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15078, uu____15079) in
              FStar_Syntax_Syntax.GTotal uu____15069 in
            {
              FStar_Syntax_Syntax.n = uu____15068;
              FStar_Syntax_Syntax.pos =
                (uu___209_15065.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___209_15065.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15131  ->
                      match uu____15131 with
                      | (a,i) ->
                          let uu____15142 = norm cfg env [] a in
                          (uu____15142, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___161_15153  ->
                      match uu___161_15153 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15157 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____15157
                      | f -> f)) in
            let uu___210_15161 = comp1 in
            let uu____15164 =
              let uu____15165 =
                let uu___211_15166 = ct in
                let uu____15167 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____15168 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____15171 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15167;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___211_15166.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15168;
                  FStar_Syntax_Syntax.effect_args = uu____15171;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____15165 in
            {
              FStar_Syntax_Syntax.n = uu____15164;
              FStar_Syntax_Syntax.pos =
                (uu___210_15161.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___210_15161.FStar_Syntax_Syntax.vars)
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
            (let uu___212_15189 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___212_15189.tcenv);
               delta_level = (uu___212_15189.delta_level);
               primitive_steps = (uu___212_15189.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____15194 = norm1 t in
          FStar_Syntax_Util.non_informative uu____15194 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____15197 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___213_15216 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.pos =
                (uu___213_15216.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___213_15216.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____15223 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____15223
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
                    let uu___214_15234 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___214_15234.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___214_15234.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___214_15234.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___215_15236 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___215_15236.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___215_15236.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___215_15236.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___215_15236.FStar_Syntax_Syntax.flags)
                    } in
              let uu___216_15237 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos =
                  (uu___216_15237.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___216_15237.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____15239 -> c
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____15242  ->
        match uu____15242 with
        | (x,imp) ->
            let uu____15245 =
              let uu___217_15246 = x in
              let uu____15247 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___217_15246.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___217_15246.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15247
              } in
            (uu____15245, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15253 =
          FStar_List.fold_left
            (fun uu____15271  ->
               fun b  ->
                 match uu____15271 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____15253 with | (nbs,uu____15299) -> FStar_List.rev nbs
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
            let uu____15315 =
              let uu___218_15316 = rc in
              let uu____15317 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___218_15316.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15317;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___218_15316.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15315
        | uu____15324 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          match stack1 with
          | [] -> t
          | (Debug (tm,time_then))::stack2 ->
              ((let uu____15337 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____15337
                then
                  let time_now = FStar_Util.now () in
                  let uu____15339 =
                    let uu____15340 =
                      let uu____15341 =
                        FStar_Util.time_diff time_then time_now in
                      FStar_Pervasives_Native.snd uu____15341 in
                    FStar_Util.string_of_int uu____15340 in
                  let uu____15346 = FStar_Syntax_Print.term_to_string tm in
                  let uu____15347 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                    uu____15339 uu____15346 uu____15347
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___219_15365 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___219_15365.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____15434  ->
                    let uu____15435 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____15435);
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
              let uu____15471 =
                let uu___220_15472 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___220_15472.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___220_15472.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____15471
          | (Arg (Univ uu____15473,uu____15474,uu____15475))::uu____15476 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____15479,uu____15480))::uu____15481 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____15497),aq,r))::stack2 ->
              (log cfg
                 (fun uu____15526  ->
                    let uu____15527 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____15527);
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
                 (let uu____15537 = FStar_ST.op_Bang m in
                  match uu____15537 with
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
                  | FStar_Pervasives_Native.Some (uu____15637,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq)
                          FStar_Pervasives_Native.None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r in
              let uu____15661 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____15661
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____15671  ->
                    let uu____15672 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____15672);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____15677 =
                  log cfg
                    (fun uu____15682  ->
                       let uu____15683 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____15684 =
                         let uu____15685 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____15702  ->
                                   match uu____15702 with
                                   | (p,uu____15712,uu____15713) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____15685
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____15683 uu____15684);
                  (let whnf1 = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___162_15730  ->
                               match uu___162_15730 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____15731 -> false)) in
                     let steps' =
                       let uu____15735 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____15735
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___221_15739 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___221_15739.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___221_15739.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf1
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____15783 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____15806 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____15872  ->
                                   fun uu____15873  ->
                                     match (uu____15872, uu____15873) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____15976 = norm_pat env3 p1 in
                                         (match uu____15976 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____15806 with
                          | (pats1,env3) ->
                              ((let uu___222_16078 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___222_16078.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___223_16097 = x in
                           let uu____16098 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___223_16097.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___223_16097.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16098
                           } in
                         ((let uu___224_16106 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___224_16106.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___225_16111 = x in
                           let uu____16112 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___225_16111.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___225_16111.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16112
                           } in
                         ((let uu___226_16120 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___226_16120.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___227_16130 = x in
                           let uu____16131 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___227_16130.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___227_16130.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____16131
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___228_16140 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___228_16140.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf1 -> branches
                     | uu____16144 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____16158 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____16158 with
                                 | (p,wopt,e) ->
                                     let uu____16178 = norm_pat env1 p in
                                     (match uu____16178 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some w
                                                ->
                                                let uu____16209 =
                                                  norm_or_whnf env2 w in
                                                FStar_Pervasives_Native.Some
                                                  uu____16209 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____16215 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____16215) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____16225) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____16230 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16231;
                        FStar_Syntax_Syntax.fv_delta = uu____16232;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____16233;
                        FStar_Syntax_Syntax.fv_delta = uu____16234;
                        FStar_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_ctor uu____16235);_}
                      -> true
                  | uu____16242 -> false in
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
                  let uu____16371 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____16371 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____16420 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____16423 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____16426 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____16445 ->
                                let uu____16446 =
                                  let uu____16447 = is_cons head1 in
                                  Prims.op_Negation uu____16447 in
                                FStar_Util.Inr uu____16446)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____16468 =
                             let uu____16469 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____16469.FStar_Syntax_Syntax.n in
                           (match uu____16468 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____16479 ->
                                let uu____16480 =
                                  let uu____16481 = is_cons head1 in
                                  Prims.op_Negation uu____16481 in
                                FStar_Util.Inr uu____16480))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____16534)::rest_a,(p1,uu____16537)::rest_p) ->
                      let uu____16581 = matches_pat t1 p1 in
                      (match uu____16581 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____16606 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____16708 = matches_pat scrutinee1 p1 in
                      (match uu____16708 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____16728  ->
                                 let uu____16729 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____16730 =
                                   let uu____16731 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____16731
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____16729 uu____16730);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____16748 =
                                        let uu____16749 =
                                          let uu____16768 =
                                            FStar_Util.mk_ref
                                              (FStar_Pervasives_Native.Some
                                                 ([], t1)) in
                                          ([], t1, uu____16768, false) in
                                        Clos uu____16749 in
                                      uu____16748 :: env2) env1 s in
                             let uu____16821 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____16821))) in
                let uu____16822 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____16822
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___163_16845  ->
                match uu___163_16845 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____16849 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____16855 -> d in
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
            let uu___229_16884 = config s e in
            {
              steps = (uu___229_16884.steps);
              tcenv = (uu___229_16884.tcenv);
              delta_level = (uu___229_16884.delta_level);
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
      fun t  -> let uu____16909 = config s e in norm_comp uu____16909 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____16918 = config [] env in norm_universe uu____16918 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let uu____16927 = config [] env in ghost_to_pure_aux uu____16927 [] c
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
        let uu____16941 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____16941 in
      let uu____16942 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____16942
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___230_16944 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___230_16944.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___230_16944.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____16947  ->
                    let uu____16948 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____16948))
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
            ((let uu____16967 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16967);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____16980 = config [AllowUnboundUniverses] env in
          norm_comp uu____16980 [] c
        with
        | e ->
            ((let uu____16987 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____16987);
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
                   let uu____17027 =
                     let uu____17028 =
                       let uu____17035 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____17035) in
                     FStar_Syntax_Syntax.Tm_refine uu____17028 in
                   mk uu____17027 t01.FStar_Syntax_Syntax.pos
               | uu____17040 -> t2)
          | uu____17041 -> t2 in
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
        let uu____17093 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____17093 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____17122 ->
                 let uu____17129 = FStar_Syntax_Util.abs_formals e in
                 (match uu____17129 with
                  | (actuals,uu____17139,uu____17140) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____17154 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____17154 with
                         | (binders,args) ->
                             let uu____17171 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____17171
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
      | uu____17181 ->
          let uu____17182 = FStar_Syntax_Util.head_and_args t in
          (match uu____17182 with
           | (head1,args) ->
               let uu____17219 =
                 let uu____17220 = FStar_Syntax_Subst.compress head1 in
                 uu____17220.FStar_Syntax_Syntax.n in
               (match uu____17219 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____17223,thead) ->
                    let uu____17249 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____17249 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____17291 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___235_17299 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___235_17299.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___235_17299.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___235_17299.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___235_17299.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___235_17299.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___235_17299.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___235_17299.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___235_17299.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___235_17299.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___235_17299.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___235_17299.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___235_17299.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___235_17299.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___235_17299.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___235_17299.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___235_17299.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___235_17299.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___235_17299.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___235_17299.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___235_17299.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___235_17299.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___235_17299.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___235_17299.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___235_17299.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___235_17299.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___235_17299.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___235_17299.FStar_TypeChecker_Env.identifier_info)
                                 }) t in
                            match uu____17291 with
                            | (uu____17300,ty,uu____17302) ->
                                eta_expand_with_type env t ty))
                | uu____17303 ->
                    let uu____17304 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___236_17312 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___236_17312.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___236_17312.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___236_17312.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___236_17312.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___236_17312.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___236_17312.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___236_17312.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___236_17312.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___236_17312.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___236_17312.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___236_17312.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___236_17312.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___236_17312.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___236_17312.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___236_17312.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___236_17312.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___236_17312.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___236_17312.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___236_17312.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___236_17312.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.type_of =
                             (uu___236_17312.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___236_17312.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___236_17312.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___236_17312.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___236_17312.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___236_17312.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___236_17312.FStar_TypeChecker_Env.identifier_info)
                         }) t in
                    (match uu____17304 with
                     | (uu____17313,ty,uu____17315) ->
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
            | (uu____17393,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____17399,FStar_Util.Inl t) ->
                let uu____17405 =
                  let uu____17408 =
                    let uu____17409 =
                      let uu____17422 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____17422) in
                    FStar_Syntax_Syntax.Tm_arrow uu____17409 in
                  FStar_Syntax_Syntax.mk uu____17408 in
                uu____17405 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____17426 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____17426 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____17453 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____17508 ->
                    let uu____17509 =
                      let uu____17518 =
                        let uu____17519 = FStar_Syntax_Subst.compress t3 in
                        uu____17519.FStar_Syntax_Syntax.n in
                      (uu____17518, tc) in
                    (match uu____17509 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____17544) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____17581) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____17620,FStar_Util.Inl uu____17621) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____17644 -> failwith "Impossible") in
              (match uu____17453 with
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
          let uu____17753 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____17753 with
          | (univ_names1,binders1,tc) ->
              let uu____17811 = FStar_Util.left tc in
              (univ_names1, binders1, uu____17811)
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
          let uu____17850 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____17850 with
          | (univ_names1,binders1,tc) ->
              let uu____17910 = FStar_Util.right tc in
              (univ_names1, binders1, uu____17910)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____17945 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____17945 with
           | (univ_names1,binders1,typ1) ->
               let uu___237_17973 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___237_17973.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___237_17973.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___237_17973.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___237_17973.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___238_17994 = s in
          let uu____17995 =
            let uu____17996 =
              let uu____18005 = FStar_List.map (elim_uvars env) sigs in
              (uu____18005, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____17996 in
          {
            FStar_Syntax_Syntax.sigel = uu____17995;
            FStar_Syntax_Syntax.sigrng =
              (uu___238_17994.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___238_17994.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___238_17994.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___238_17994.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____18022 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18022 with
           | (univ_names1,uu____18040,typ1) ->
               let uu___239_18054 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___239_18054.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___239_18054.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___239_18054.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___239_18054.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____18060 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____18060 with
           | (univ_names1,uu____18078,typ1) ->
               let uu___240_18092 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_18092.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_18092.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_18092.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_18092.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____18126 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____18126 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____18149 =
                            let uu____18150 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____18150 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____18149 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___241_18153 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___241_18153.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___241_18153.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___242_18154 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___242_18154.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___242_18154.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___242_18154.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___242_18154.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___243_18166 = s in
          let uu____18167 =
            let uu____18168 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____18168 in
          {
            FStar_Syntax_Syntax.sigel = uu____18167;
            FStar_Syntax_Syntax.sigrng =
              (uu___243_18166.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___243_18166.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___243_18166.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___243_18166.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____18172 = elim_uvars_aux_t env us [] t in
          (match uu____18172 with
           | (us1,uu____18190,t1) ->
               let uu___244_18204 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___244_18204.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___244_18204.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___244_18204.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___244_18204.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18205 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____18207 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____18207 with
           | (univs1,binders,signature) ->
               let uu____18235 =
                 let uu____18244 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____18244 with
                 | (univs_opening,univs2) ->
                     let uu____18271 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____18271) in
               (match uu____18235 with
                | (univs_opening,univs_closing) ->
                    let uu____18288 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____18294 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____18295 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____18294, uu____18295) in
                    (match uu____18288 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____18317 =
                           match uu____18317 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____18335 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____18335 with
                                | (us1,t1) ->
                                    let uu____18346 =
                                      let uu____18351 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____18358 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____18351, uu____18358) in
                                    (match uu____18346 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____18371 =
                                           let uu____18376 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____18385 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____18376, uu____18385) in
                                         (match uu____18371 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____18401 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____18401 in
                                              let uu____18402 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____18402 with
                                               | (uu____18423,uu____18424,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____18439 =
                                                       let uu____18440 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____18440 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____18439 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____18445 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____18445 with
                           | (uu____18458,uu____18459,t1) -> t1 in
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
                             | uu____18519 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____18536 =
                               let uu____18537 =
                                 FStar_Syntax_Subst.compress body in
                               uu____18537.FStar_Syntax_Syntax.n in
                             match uu____18536 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____18596 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____18625 =
                               let uu____18626 =
                                 FStar_Syntax_Subst.compress t in
                               uu____18626.FStar_Syntax_Syntax.n in
                             match uu____18625 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____18647) ->
                                 let uu____18668 = destruct_action_body body in
                                 (match uu____18668 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____18713 ->
                                 let uu____18714 = destruct_action_body t in
                                 (match uu____18714 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____18763 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____18763 with
                           | (action_univs,t) ->
                               let uu____18772 = destruct_action_typ_templ t in
                               (match uu____18772 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___245_18813 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___245_18813.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___245_18813.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___246_18815 = ed in
                           let uu____18816 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____18817 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____18818 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____18819 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____18820 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____18821 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____18822 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____18823 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____18824 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____18825 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____18826 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____18827 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____18828 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____18829 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___246_18815.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___246_18815.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____18816;
                             FStar_Syntax_Syntax.bind_wp = uu____18817;
                             FStar_Syntax_Syntax.if_then_else = uu____18818;
                             FStar_Syntax_Syntax.ite_wp = uu____18819;
                             FStar_Syntax_Syntax.stronger = uu____18820;
                             FStar_Syntax_Syntax.close_wp = uu____18821;
                             FStar_Syntax_Syntax.assert_p = uu____18822;
                             FStar_Syntax_Syntax.assume_p = uu____18823;
                             FStar_Syntax_Syntax.null_wp = uu____18824;
                             FStar_Syntax_Syntax.trivial = uu____18825;
                             FStar_Syntax_Syntax.repr = uu____18826;
                             FStar_Syntax_Syntax.return_repr = uu____18827;
                             FStar_Syntax_Syntax.bind_repr = uu____18828;
                             FStar_Syntax_Syntax.actions = uu____18829
                           } in
                         let uu___247_18832 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___247_18832.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___247_18832.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___247_18832.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___247_18832.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___164_18849 =
            match uu___164_18849 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____18876 = elim_uvars_aux_t env us [] t in
                (match uu____18876 with
                 | (us1,uu____18900,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___248_18919 = sub_eff in
            let uu____18920 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____18923 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___248_18919.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___248_18919.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____18920;
              FStar_Syntax_Syntax.lift = uu____18923
            } in
          let uu___249_18926 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___249_18926.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___249_18926.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___249_18926.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___249_18926.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____18936 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____18936 with
           | (univ_names1,binders1,comp1) ->
               let uu___250_18970 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___250_18970.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___250_18970.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___250_18970.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___250_18970.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____18981 -> s